"""linear_combination — Phase X corpus benchmark.

Pointwise linear combination: C[k] = a*A[k] + b*B[k].  Two
scalar coefficients plus two arrays.  More general than
add_arrays or array_double; tests that the synthesizer handles
mixed scalar/array coefficients in the post-condition.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  C[k] == a*A[k] + b*B[k]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A and B, two integer coefficients "
        "a and b, an integer array C, and a length n (with n >= 0), "
        "populate C so that C[k] equals a * A[k] + b * B[k] for "
        "every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("a", "int", "input"),
                Var("b", "int", "input"),
                Var("C", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, "
                "C[k] == a*A[k] + b*B[k]))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "C[k] == a*A[k] + b*B[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"C": "Update(C, i, a*A[i] + b*B[i])", "i": "i + 1"}],

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
