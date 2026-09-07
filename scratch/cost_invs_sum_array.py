"""cost_invs_sum_array.py — first-slice manual Z3 encoding of a
cost-invariant proof obligation, validating the COST_INVS.md
design before plumbing it into the synth framework.

Benchmark: a sum_array-style loop.
  i := 0;
  s := 0;
  while (i < n) {              // tau@L, phi@L, cost@L
      s := s + A[i];           // body cost = 1
      i := i + 1;
  }

Expected cost: O(n).

Design under test (COST_INVS.md §1):
  cost@L  — a Real- or Int-valued "remaining cost budget"
            expression in pre-state vars.  Decreases per iter.
  cost_per_iter(body) — # of primitive ops per iteration (= 1 here).

Constraints we want Z3 to verify (analogous to phi@L's ranking):
  (A) Non-negativity:  cost@L(state) ≥ 0  at every reachable state.
  (B) Decrement     :  cost@L(pre) ≥ cost_per_iter + cost@L(post)
                       for every τ-consistent, guard-satisfying
                       (pre, post) pair.
  (C) Initial budget:  cost@L(initial state) ≤ cost_target(inputs).

If Z3 finds a valid cost@L given a `cost_target`, that proves the
loop's total cost ≤ cost_target.

We model cost@L as a hole over a finite candidate list (same
shape as phi@L's candidate list in our synth framework).  This
script asks Z3:
  - "Does cost@L = n - i, with cost_target = n, satisfy A/B/C?"
    → expected SAT.
  - "Does cost@L = n - i - 1, with cost_target = n - 1, work?"
    → expected UNSAT (loop runs n times, not n - 1).
  - "Does cost@L = i, with cost_target = n, work?"
    → expected UNSAT (cost@L should DECREASE, not INCREASE).

Each is encoded as a Z3 query and the verdict reported.

This is a SCRATCH validation script (per the feedback memory:
scratch/ dir for codegen).  It does NOT yet wire cost@L into
the synth framework.  After this validates, the next step is to
add `cost@L` allocation to expand.py + constraint emission to
constraints.py.
"""
from z3 import (And, Bool, BoolVal, ForAll, Implies, Int, IntVal,
                Not, Or, Solver, sat, unsat, set_param)


def check_cost_invariant(
    cost_at_L,           # function: (i, n) → Int  for the cost@L candidate
    cost_target,         # function: n → Int  for the cost target
    label,
):
    """Verify (A), (B), (C) for the chosen cost@L candidate and cost_target.

    Args are functions returning Z3 Int expressions over fresh i, n vars.
    """
    print(f"\n=== {label} ===")

    # Symbolic state: pre = (i, n) with τ_inv asserted; post = (i', n).
    i  = Int("i")
    n  = Int("n")
    ip = Int("ip")          # i' = i + 1

    # τ@L invariant we'd want the synth to discover: 0 ≤ i ≤ n.
    # (We're hand-encoding the same shape as our sum_array benchmark.)
    tau_inv  = And(0 <= i, i <= n)
    tau_inv_post = And(0 <= ip, ip <= n)
    guard    = i < n
    trans_i  = ip == i + 1

    cost_per_iter = IntVal(1)
    cost_pre  = cost_at_L(i, n)
    cost_post = cost_at_L(ip, n)
    target    = cost_target(n)

    # Pre on inputs: n ≥ 0 (typical).
    pre_inputs = n >= 0

    # (A) Non-negativity at reachable state.
    # We assert τ@L ∧ pre_inputs ⇒ cost@L ≥ 0.
    s_A = Solver()
    s_A.add(pre_inputs, tau_inv)
    s_A.add(Not(cost_pre >= 0))
    r_A = s_A.check()
    a_ok = (r_A == unsat)
    print(f"  (A) Non-negativity: {'OK' if a_ok else 'FAIL'} ({r_A})")

    # (B) Decrement: τ ∧ guard ∧ trans ⇒ cost_pre ≥ 1 + cost_post.
    s_B = Solver()
    s_B.add(pre_inputs, tau_inv, guard, trans_i)
    s_B.add(Not(cost_pre >= cost_per_iter + cost_post))
    r_B = s_B.check()
    b_ok = (r_B == unsat)
    print(f"  (B) Decrement     : {'OK' if b_ok else 'FAIL'} ({r_B})")
    if not b_ok:
        m = s_B.model()
        print(f"      counter-example: i={m.eval(i)}, n={m.eval(n)}, "
              f"cost_pre={m.eval(cost_pre)}, cost_post={m.eval(cost_post)}")

    # (C) Initial budget: Pre(inputs) ⇒ cost_at_L(initial i=0) ≤ target.
    # Initial state has i = 0.
    s_C = Solver()
    s_C.add(pre_inputs)
    initial_cost = cost_at_L(IntVal(0), n)
    s_C.add(Not(initial_cost <= target))
    r_C = s_C.check()
    c_ok = (r_C == unsat)
    print(f"  (C) Initial budget: {'OK' if c_ok else 'FAIL'} ({r_C})")
    if not c_ok:
        m = s_C.model()
        print(f"      counter-example: n={m.eval(n)}, "
              f"cost_at_init={m.eval(initial_cost)}, target={m.eval(target)}")

    all_ok = a_ok and b_ok and c_ok
    print(f"  → Total: {'VERIFIED' if all_ok else 'REJECTED'}")
    return all_ok


def main():
    set_param("parallel.enable", True)

    print("COST_INVS first-slice scratch validation.")
    print("Loop:  while (i < n) { body cost 1; i++ }")
    print("Expected: cost@L = n - i with cost_target = n  SHOULD VERIFY.\n")

    # ---- Case 1: cost@L = n - i, cost_target = n.  Expected: VERIFY.
    case_1 = check_cost_invariant(
        cost_at_L=lambda i, n: n - i,
        cost_target=lambda n: n,
        label="cost@L = n - i, cost_target = n  (expected VERIFY)",
    )

    # ---- Case 2: cost@L = n - i - 1, cost_target = n - 1.  Expected: REJECT.
    # Loop runs n times; one less than n - 1 can't cover (A) at boundary
    # when n=0 (cost = -1 < 0).
    case_2 = check_cost_invariant(
        cost_at_L=lambda i, n: n - i - 1,
        cost_target=lambda n: n - 1,
        label="cost@L = n - i - 1, cost_target = n - 1  (expected REJECT)",
    )

    # ---- Case 3: cost@L = i, cost_target = n.  Expected: REJECT (increasing).
    case_3 = check_cost_invariant(
        cost_at_L=lambda i, n: i,
        cost_target=lambda n: n,
        label="cost@L = i, cost_target = n  (expected REJECT, increasing)",
    )

    # ---- Case 4: cost@L = 2*(n - i), cost_target = 2*n.  Expected: VERIFY
    # (looser bound that still works).
    case_4 = check_cost_invariant(
        cost_at_L=lambda i, n: 2 * (n - i),
        cost_target=lambda n: 2 * n,
        label="cost@L = 2*(n - i), cost_target = 2*n  (expected VERIFY)",
    )

    # ---- Case 5: cost@L = n - i, cost_target = n - 1.  Expected: REJECT
    # (target too tight by 1).
    case_5 = check_cost_invariant(
        cost_at_L=lambda i, n: n - i,
        cost_target=lambda n: n - 1,
        label="cost@L = n - i, cost_target = n - 1  (expected REJECT, target too tight)",
    )

    print("\n" + "=" * 50)
    print("Summary:")
    cases = [
        ("Case 1: cost@L = n-i, target = n",        case_1, "VERIFY"),
        ("Case 2: cost@L = n-i-1, target = n-1",    case_2, "REJECT"),
        ("Case 3: cost@L = i (increasing)",         case_3, "REJECT"),
        ("Case 4: cost@L = 2(n-i), target = 2n",    case_4, "VERIFY"),
        ("Case 5: cost@L = n-i, target = n-1",      case_5, "REJECT"),
    ]
    all_match = True
    for label, actual, expected in cases:
        actual_str = "VERIFY" if actual else "REJECT"
        match = (actual_str == expected)
        all_match = all_match and match
        mark = "✓" if match else "✗"
        print(f"  {mark} {label:50s} → {actual_str} (expected {expected})")

    print()
    if all_match:
        print("All cases match expected outcomes — COST_INVS encoding")
        print("validated for the sum_array shape.  Ready for §1 IR plumbing.")
        return 0
    else:
        print("MISMATCH — encoding needs revision.")
        return 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
