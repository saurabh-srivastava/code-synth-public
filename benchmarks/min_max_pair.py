"""min_max_pair — Phase X corpus benchmark.

Return BOTH the min and max of A[0..n) in a single pass.
Different shape from max_min_diff (which returns the
difference): this returns two scalar outputs simultaneously,
testing multi-output return semantics with quantified
invariants on both.

Spec:
    Pre  : n >= 1
    Post : ForAll k. 0 ≤ k < n ⇒ mn <= A[k] <= mx
         ∧ ∃k. A[k] == mn
         ∧ ∃k. A[k] == mx
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 1), "
        "return BOTH the minimum and maximum values among "
        "A[0], A[1], ..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("mn", "int", "output"),
                Var("mx", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "n >= 1",
    post     = (
        "ForAll(lambda k: Implies("
        "0 <= k and k < n, mn <= A[k] and A[k] <= mx)) and "
        "Exists(lambda k: 0 <= k and k < n and A[k] == mn) and "
        "Exists(lambda k: 0 <= k and k < n and A[k] == mx)"
    ),

    atoms = {
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

        # Branch 0: A[i] < mn → tighten mn.
        "g@B1.0": ["A[i] < mn"],
        "s@B1.0": [{"mn": "A[i]", "i": "i + 1"}],
        # Branch 1: A[i] >= mn → maybe extend mx.
        "g@B1.1": ["A[i] >= mn"],
        "s@B1.1": [{
            "mx": "mx if A[i] <= mx else A[i]",
            "i": "i + 1",
        }],
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
