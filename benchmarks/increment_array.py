"""increment_array — Phase X corpus benchmark.

Pointwise increment: B[k] = A[k] + 1 for each k in [0, n).  A
two-array element-wise transform.  Tests the synthesizer on a
pattern where the post-condition relates input and output array
values directly (not just an absolute value like `array_zero`).

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  B[k] == A[k] + 1
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, an integer array B, and a length "
        "n (with n >= 0), populate B so that B[k] equals A[k] + 1 "
        "for every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k] + 1))",

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "ForAll(lambda k: Implies(0 <= k and k < i, B[k] == A[k] + 1))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"B": "Update(B, i, A[i] + 1)", "i": "i + 1"}],

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
