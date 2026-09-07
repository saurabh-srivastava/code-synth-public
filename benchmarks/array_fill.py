"""array_fill — Phase X corpus benchmark.

Fill an integer array with a given value.  Generalizes
`array_zero` (which fills with 0) to an arbitrary fill value
passed as input.  Pure SMT-tractable; no UF axioms.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  A[k] == v
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n (with n >= 0), and a "
        "fill value v, modify A so that A[0], A[1], ..., A[n-1] all "
        "equal v."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("v", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == v))",

    atoms = {
        # Entry: i := 0
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "ForAll(lambda k: Implies(0 <= k and k < i, A[k] == v))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Body: A[i] := v; i := i + 1
        "s@B1": [{"A": "Update(A, i, v)", "i": "i + 1"}],

        # Exit: identity
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
