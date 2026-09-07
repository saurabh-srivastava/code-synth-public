"""array_max_val — Phase X corpus benchmark.

Return the maximum VALUE in A[0..n) (not the index, unlike
`array_max_index`).  Similar template to `max_array` but with
a cleaner two-branch SB(n=2) inner body.

Spec:
    Pre  : n >= 1
    Post : (∀k. 0 ≤ k < n ⇒ A[k] <= m) ∧ ∃k. 0 ≤ k < n ∧ A[k] == m
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 1), "
        "return the maximum value among A[0], A[1], ..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "n >= 1",
    post     = (
        "ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= m)) and "
        "Exists(lambda k: 0 <= k and k < n and A[k] == m)"
    ),

    atoms = {
        # Init from A[0].
        "s@B0": [{"m": "A[0]", "i": "1"}],

        "tau@L0": [
            "1 <= i",
            "i <= n",
            "n >= 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] <= m))"),
            ("Exists(lambda k: 0 <= k and k < i and A[k] == m)"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] > m → m := A[i].
        "g@B1.0": ["A[i] > m"],
        "s@B1.0": [{"m": "A[i]", "i": "i + 1"}],
        # Branch 1: A[i] <= m → no change.
        "g@B1.1": ["A[i] <= m"],
        "s@B1.1": [{"i": "i + 1"}],
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
