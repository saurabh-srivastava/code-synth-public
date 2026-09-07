"""max2 — Phase X corpus benchmark.

Scalar binary max — the simplest acyclic conditional shape.
Tests the synthesizer on a pure scalar problem with no arrays
and no loops (just an SB(n=2) branch).

Spec:
    Pre  : true
    Post : result >= a ∧ result >= b ∧ (result == a ∨ result == b)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integers a and b, return the larger of the two "
        "(the maximum)."
    ),

    template = SB(n=2),
    inputs   = [Var("a", "int", "input"), Var("b", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    post     = ("(result >= a) and (result >= b) and "
                "((result == a) or (result == b))"),

    atoms = {
        # Branch 0 (a >= b): result := a
        "g@B0.0": ["a >= b", "a > b", "a == b"],
        "s@B0.0": [{"result": "a"}],
        # Branch 1 (else, a < b): result := b
        "g@B0.1": ["a < b", "a <= b", "b >= a"],
        "s@B0.1": [{"result": "b"}],
    },
    max_solutions = 5,
    expected_solutions = 5,
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
