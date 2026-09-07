"""range_init_offset — Phase X corpus benchmark.

Variant of `range_init` where A[k] := k + offset for an offset
parameter.  Loop with quantified prefix-equal invariant.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n ⇒ A[k] == k + offset
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-negative integer n, an offset, and an integer "
        "array A, set A[k] := k + offset for every k in 0..n-1."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("offset", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre  = "n >= 0",
    post = ("ForAll(lambda k: Implies("
            "0 <= k and k < n, A[k] == k + offset))"),

    atoms = {
        "s@B0": [{"i": "0"}],
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] == k + offset))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "s@B1": [{"A": "Update(A, i, i + offset)", "i": "i + 1"}],
        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
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
