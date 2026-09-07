"""cost_invs_nested.py — second-slice validation for nested loops.

Validates that a NESTED loop's cost composes correctly.

Benchmark: bubble-sort-style nested loop shape.
  i := 0;
  while (i < n) {                  // tau@L0, phi@L0, cost@L0
      j := 0;
      while (j < n - 1 - i) {      // tau@L1, phi@L1, cost@L1
          // body cost 1
          j := j + 1;
      }
      i := i + 1;
  }

Total cost: sum_{i=0..n-1} (n - 1 - i) = n(n-1)/2 = O(n²).

For each outer iteration i:
  - Inner loop runs (n - 1 - i) times.
  - Inner total cost (from cost@L1) at the START of body: cost@L1(j=0) = n - 1 - i.

So cost@L0 should reflect:
  cost@L0(state) = remaining inner-cost contributions + outer overhead.

Specifically, total cost from outer iter i onward:
  Σ_{k=i..n-1} (n - 1 - k) = (n - 1 - i)(n - i) / 2.

That's quadratic.  Let's see if Z3 handles candidate
  cost@L0(i, n) = (n - 1 - i) * (n - i) / 2

The standard worst-case bound is n*(n-1)/2 ≤ n²/2 ≤ n².
A tighter target: cost ≤ n² / 2  or  cost ≤ n * (n - 1) / 2.

Note: integer division.  We use 2*cost ≤ ... to avoid division.

Encoding:
  cost@L1 = (n - 1 - i) - j        (per-iter cost in inner loop)
  cost@L0 = ???                     (must aggregate inner contributions)

A clean way to encode the AGGREGATION: introduce a "remaining
total cost" function.  At outer entry-i:
  remaining(i, n) = Σ_{k=i..n-1} inner_cost(k) = (n-1-i)(n-i)/2

Then cost@L0(i, n) ≥ remaining(i, n).

For the body of the outer loop (one full inner-loop execution):
  cost@L0(i_pre, n) ≥ inner_total_cost(i_pre, n) + cost@L0(i_post, n)
  where i_post = i_pre + 1 and inner_total_cost(i_pre, n) = n - 1 - i_pre.

Rearranged:
  cost@L0(i, n) - cost@L0(i+1, n) ≥ (n - 1 - i)

For cost@L0 = (n-i)(n-1-i)/2:
  cost@L0(i, n) - cost@L0(i+1, n)
  = (n-i)(n-1-i)/2 - (n-i-1)(n-i-2)/2
  = [(n-i)(n-1-i) - (n-i-1)(n-i-2)] / 2
  = [ ... let's expand:
      (n-i)(n-1-i) = (n-i)² - (n-i)
      (n-i-1)(n-i-2) = (n-i-1)² - (n-i-1) = (n-i)² - 2(n-i) + 1 - (n-i) + 1 = (n-i)² - 3(n-i) + 2
      diff = -(n-i) - (-3(n-i) + 2) = -(n-i) + 3(n-i) - 2 = 2(n-i) - 2 ]
  = (2(n-i) - 2) / 2 = n - i - 1.

So cost@L0(i) - cost@L0(i+1) = n - i - 1, which matches the inner
loop's iter count n - 1 - i.  ✓ (B) holds with equality.

We avoid Z3 division by encoding:
  2 * cost@L0(i, n) = (n - i) * (n - 1 - i)

This script encodes the obligations.  Per (A), (B), (C):
  (A) cost@L0 ≥ 0  and  cost@L1 ≥ 0  at reachable states.
  (B) cost@L0(i, n) - cost@L0(i+1, n) ≥ inner_total_cost(i, n).
  (B') cost@L1(i, j, n) - cost@L1(i, j+1, n) ≥ 1  (inner body cost).
  (C) cost@L0(0, n) ≤ cost_target.

Expected: cost_target = n*(n-1)/2  (= sum of inner counts).
"""
from z3 import (And, Bool, BoolVal, Implies, Int, IntVal,
                Not, Or, Solver, sat, unsat, set_param)


def make_cost_at_L0_pair(form):
    """Return (cost@L0, cost@L1) pair for the named form."""
    if form == "quadratic":
        # 2 * cost@L0 = (n - i) * (n - 1 - i).
        # We don't use division; express as 2*cost in constraints.
        cost_L0 = lambda i, n: (n - i) * (n - 1 - i)   # = 2 * actual cost
        cost_L1 = lambda i, j, n: (n - 1 - i) - j      # actual cost
        scale_L0 = 2
        return cost_L0, cost_L1, scale_L0
    raise ValueError(form)


def check_nested(form):
    print(f"\n=== Nested-loop cost: form = {form} ===")

    cost_L0, cost_L1, scale_L0 = make_cost_at_L0_pair(form)

    i  = Int("i");  ip = Int("ip")
    j  = Int("j");  jp = Int("jp")
    n  = Int("n")

    pre_inputs = n >= 0
    tau_L0  = And(0 <= i, i <= n)
    guard_L0 = i < n
    trans_outer = And(ip == i + 1, jp == j)   # j gets reset inside; not used here.

    tau_L1  = And(0 <= i, i < n, 0 <= j, j <= n - 1 - i)
    guard_L1 = j < n - 1 - i

    # ----- L1 obligations.
    # (A_L1) Non-negativity: tau_L1 ⇒ cost_L1 ≥ 0.
    s = Solver()
    s.add(pre_inputs, tau_L1)
    s.add(Not(cost_L1(i, j, n) >= 0))
    a_L1 = s.check() == unsat
    print(f"  (A_L1) cost_L1 ≥ 0       : {'OK' if a_L1 else 'FAIL'}")

    # (B_L1) Decrement: tau_L1 ∧ guard_L1 ⇒ cost_L1(j) - cost_L1(j+1) ≥ 1.
    s = Solver()
    s.add(pre_inputs, tau_L1, guard_L1)
    s.add(Not(cost_L1(i, j, n) - cost_L1(i, j + 1, n) >= 1))
    b_L1 = s.check() == unsat
    print(f"  (B_L1) decrement ≥ 1     : {'OK' if b_L1 else 'FAIL'}")

    # ----- L0 obligations.
    # (A_L0) Non-negativity at outer reachable: tau_L0 ⇒ scale_L0 * cost_L0 ≥ 0.
    s = Solver()
    s.add(pre_inputs, tau_L0)
    s.add(Not(cost_L0(i, n) >= 0))
    a_L0 = s.check() == unsat
    print(f"  (A_L0) cost_L0 ≥ 0       : {'OK' if a_L0 else 'FAIL'}")

    # (B_L0) Decrement covers inner cost:
    # tau_L0 ∧ guard_L0 ⇒ (cost_L0(i) - cost_L0(i+1)) ≥ scale_L0 * inner_total_cost(i, n).
    # inner_total_cost(i, n) = cost_L1(i, 0, n) = n - 1 - i.
    s = Solver()
    s.add(pre_inputs, tau_L0, guard_L0)
    s.add(Not(cost_L0(i, n) - cost_L0(ip, n) >= scale_L0 * (n - 1 - i)))
    s.add(ip == i + 1)
    b_L0 = s.check() == unsat
    print(f"  (B_L0) decrement covers inner: {'OK' if b_L0 else 'FAIL'}")
    if not b_L0:
        m = s.model()
        print(f"      counter-example: i={m.eval(i)}, n={m.eval(n)}")

    # (C) Initial budget: cost_L0(0, n) ≤ scale_L0 * target.
    # Target = n * (n - 1) / 2  ⇒  2 * target = n * (n - 1).
    s = Solver()
    s.add(pre_inputs)
    target_scaled = n * (n - 1)   # = scale_L0 * actual target
    s.add(Not(cost_L0(IntVal(0), n) <= target_scaled))
    c_ok = s.check() == unsat
    print(f"  (C) cost_L0(0) ≤ 2*target: {'OK' if c_ok else 'FAIL'}")

    all_ok = a_L1 and b_L1 and a_L0 and b_L0 and c_ok
    print(f"  → Total: {'VERIFIED' if all_ok else 'REJECTED'}")
    return all_ok


def main():
    set_param("parallel.enable", True)
    print("COST_INVS second-slice validation: nested loop (bubble-sort shape).")
    print("Total cost target: n*(n-1)/2 = O(n²).")

    ok = check_nested("quadratic")
    print()
    if ok:
        print("Nested-loop cost composition VERIFIED — design extends to O(n²).")
        return 0
    return 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
