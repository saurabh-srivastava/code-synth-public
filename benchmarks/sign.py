"""sign — Phase X corpus benchmark.

Return the sign of an integer: -1 if negative, 0 if zero, 1 if
positive.  SB(n=3).

Spec:
    Pre  : true
    Post : ((x > 0) ∧ s == 1) ∨ ((x == 0) ∧ s == 0) ∨ ((x < 0) ∧ s == -1)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x, return its sign: 1 if x > 0, -1 if "
        "x < 0, 0 if x == 0."
    ),

    template = SB(n=3),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    pre      = "true",
    post     = (
        "((x > 0) and (s == 1)) or "
        "((x == 0) and (s == 0)) or "
        "((x < 0) and (s == 0 - 1))"
    ),
    atoms = {
        "g@B0.0": ["x > 0"],
        "s@B0.0": [{"s": "1"}],
        "g@B0.1": ["x == 0"],
        "s@B0.1": [{"s": "0"}],
        "g@B0.2": ["x < 0"],
        "s@B0.2": [{"s": "0 - 1"}],
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
