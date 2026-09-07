"""abs2 — Phase X corpus benchmark.

Squared absolute value: |x| * |x| = x * x (no branching needed
because squaring is sign-agnostic).  Pure acyclic; tests that
the synthesizer can recognize the simplification.

Spec:
    Pre  : true
    Post : (y >= 0) ∧ (y == x * x)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x, return |x| squared, which equals x * x."
    ),

    template = SB(n=1),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("y", "int", "output")],
    pre      = "true",
    post     = "(y >= 0) and (y == x * x)",
    atoms = {
        "s@B0": [{"y": "x * x"}],
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
