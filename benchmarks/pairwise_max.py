"""pairwise_max — Phase X corpus benchmark.

Element-wise max of two integer arrays: C[k] = max(A[k], B[k]).
Like clamp_array_positive but with a more meaningful comparison —
tests SB(n=2) inside Loop with both branches writing to the same
output array via different sources.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒
           ((A[k] >= B[k] ∧ C[k] == A[k]) ∨
            (A[k] < B[k] ∧ C[k] == B[k]))
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A and B, an integer array C, and a "
        "length n (with n >= 0), populate C so that C[k] equals the "
        "larger of A[k] and B[k] for every k in [0, n)."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("C", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, "
                "((A[k] >= B[k] and C[k] == A[k]) or "
                " (A[k] < B[k] and C[k] == B[k]))))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "((A[k] >= B[k] and C[k] == A[k]) or "
             " (A[k] < B[k] and C[k] == B[k]))))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] >= B[i] → C[i] := A[i]
        "g@B1.0": ["A[i] >= B[i]", "A[i] > B[i]"],
        "s@B1.0": [{"C": "Update(C, i, A[i])", "i": "i + 1"}],
        # Branch 1: else → C[i] := B[i]
        "g@B1.1": ["A[i] < B[i]", "A[i] <= B[i]"],
        "s@B1.1": [{"C": "Update(C, i, B[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 2,
    expected_solutions = 2,
    expected_lean_hits = 0,
    solver_timeout_ms = 180_000,
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
