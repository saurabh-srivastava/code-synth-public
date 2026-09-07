"""add_arrays — Phase X corpus benchmark.

Pointwise sum of two integer arrays into a third: C[k] = A[k] + B[k]
for k in [0, n).  Three-array shape — A and B are read-only, C is
the output.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  C[k] == A[k] + B[k]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A and B and a length n (with n >= 0), "
        "populate a third integer array C so that C[k] equals A[k] + B[k] "
        "for every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("C", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, "
                "C[k] == A[k] + B[k]))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "C[k] == A[k] + B[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"C": "Update(C, i, A[i] + B[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 2,
    expected_solutions = 2,
    expected_lean_hits = 0,
    solver_timeout_ms = 120_000,
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
