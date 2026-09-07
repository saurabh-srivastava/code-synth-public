"""bubble_sort_cost — cost-bound variant of bubble_sort.

Quadratic-cost nested-loop benchmark.  Outer body =
Seq(SB_j_init, Loop_inner, SB_i_step); inner body = SB(n=2)
conditional swap.

Per outer iteration:
  SB1 (j := 0)            cost 1
  Loop_inner                cost = cost@L1(j = 0) = n - 1 - i
  SB3 (i := i + 1)        cost 1
Outer body cost = 2 + (n - 1 - i) = n + 1 - i.

Total cost = Σ_{i=0..n-1} (n + 1 - i) = n(n+1)/2.

We use a slightly loose UPPER bound:
  cost@L0 = (n - i) * (n - i + 1)  → per-iter decrease 2(n - i).
  Since 2(n - i) ≥ n + 1 - i for i < n (equivalent to n ≥ i + 1, true
  by outer guard), this bound is admissible.
  cost@L0(0) = n * (n + 1).

cost_target = "n * (n + 1)".

This is COST_INVS §1.5's first nontrivial nested-loop test —
the inner loop's iteration count depends on the OUTER loop's
index variable i (n - 1 - i), creating a genuine quadratic
accumulation.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB() >> Loop(SB(n=2)) >> SB()),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local"), Var("j", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda p, q: Implies(0 <= p and p <= q and "
                "q < n, A[p] <= A[q]))"),
    cost_target = "n * (n + 1)",
    atoms = {
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            ("ForAll(lambda p, q: Implies(0 <= p and p <= q and "
             "q < n and q >= n - i, A[p] <= A[q]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "cost@L0": [
            "(n - i) * (n - i + 1)",        # ← published, quadratic
            "n - i",                         # too small for body cost
            "n * (n + 1)",                   # constant; fails (B)
        ],
        "tau@L1": [
            "0 <= j",
            "j <= n - 1 - i",
            "i < n",
            "n >= 0",
            ("ForAll(lambda p, q: Implies(0 <= p and p <= q and "
             "q < n and q >= n - i, A[p] <= A[q]))"),
            ("ForAll(lambda k: Implies(0 <= k and k <= j, "
             "A[k] <= A[j]))"),
        ],
        "g@L1":   ["j < n - 1 - i"],
        "phi@L1": ["n - 1 - i - j"],
        "cost@L1": [
            "n - 1 - i - j",                 # ← published
            "n - i",                         # fails (B): decrement off
            "n",                             # fails (B): constant
        ],
        "s@B0":   [{"i": "0"}],
        "s@B1":   [{"j": "0"}],
        "g@B2.0": ["A[j] > A[j + 1]"],
        "g@B2.1": ["A[j] <= A[j + 1]"],
        "s@B2.0": [{"A": "Update(Update(A, j, A[j + 1]), j + 1, A[j])",
                    "j": "j + 1"}],
        "s@B2.1": [{"j": "j + 1"}],
        "s@B3":   [{"i": "i + 1"}],
    },
    max_solutions = 3,
    expected_solutions = None,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    elapsed = time.monotonic() - t
    print(f"wall: {elapsed:.1f}s")
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for k, sol in enumerate(result.solutions[:3]):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
