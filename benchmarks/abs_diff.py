"""abs_diff — Phase X corpus benchmark.

Absolute difference of two scalars: |x - y|.  Two-branch SB(n=2)
where the guard is the sign comparison.  Distinct from `abs.py`
which is unary.

Spec:
    Pre  : true
    Post : (d >= 0) ∧ ((d == x - y) ∨ (d == y - x))
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integers x and y, return the absolute value of "
        "their difference, |x - y|."
    ),

    template = SB(n=2),
    inputs   = [Var("x", "int", "input"),
                Var("y", "int", "input")],
    outputs  = [Var("d", "int", "output")],
    pre      = "true",
    post     = ("(d >= 0) and ((d == x - y) or (d == y - x))"),
    atoms = {
        # Branch 0: x >= y → d := x - y
        "g@B0.0": ["x >= y"],
        "s@B0.0": [{"d": "x - y"}],
        # Branch 1: x < y → d := y - x
        "g@B0.1": ["x < y"],
        "s@B0.1": [{"d": "y - x"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 60_000,
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
