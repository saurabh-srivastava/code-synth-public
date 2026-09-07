"""max_min_diff — Phase X corpus benchmark.

Compute `max(A) - min(A)` over the first n elements via a single
pass with two-output reduction (tracks both running max and
running min).  Tests multi-output loop reductions.

Spec:
    Pre  : n >= 1
    Post : ForAll k. 0 ≤ k < n ⇒ A[k] >= mn
         ∧ ForAll k. 0 ≤ k < n ⇒ A[k] <= mx
         ∧ ∃k. 0 ≤ k < n ∧ A[k] == mn
         ∧ ∃k. 0 ≤ k < n ∧ A[k] == mx
         ∧ d == mx - mn
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 1), "
        "return the difference between the maximum and minimum "
        "values among A[0], A[1], ..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("d", "int", "output")],
    locals   = [Var("mn", "int", "local"),
                Var("mx", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n >= 1",
    # Both mn and mx are witnessed bounds over the array slice,
    # and d is their difference.
    post     = (
        "ForAll(lambda k: Implies("
        "0 <= k and k < n, mn <= A[k] and A[k] <= mx)) and "
        "Exists(lambda k: 0 <= k and k < n and A[k] == mn) and "
        "Exists(lambda k: 0 <= k and k < n and A[k] == mx) and "
        "(d == mx - mn)"
    ),

    atoms = {
        # Init from A[0].
        "s@B0": [{"mn": "A[0]", "mx": "A[0]", "i": "1"}],

        "tau@L0": [
            "1 <= i",
            "i <= n",
            "n >= 1",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "mn <= A[k] and A[k] <= mx))"),
            ("Exists(lambda k: 0 <= k and k < i and A[k] == mn)"),
            ("Exists(lambda k: 0 <= k and k < i and A[k] == mx)"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] < mn → mn := A[i].
        "g@B1.0": ["A[i] < mn"],
        "s@B1.0": [{"mn": "A[i]", "i": "i + 1"}],
        # Branch 1: A[i] >= mn → check if A[i] > mx (combined cases).
        # Simpler: split further?  For correctness, branch 1 covers
        # "A[i] >= mn" — either still ≤ mx or now > mx.  We need
        # update of mx in the latter case.  Use a single transition
        # that uses an if-expr.
        "g@B1.1": ["A[i] >= mn"],
        "s@B1.1": [{
            "mx": "mx if A[i] <= mx else A[i]",
            "i": "i + 1",
        }],

        # Final: d := mx - mn.
        "s@B2": [{"d": "mx - mn"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
