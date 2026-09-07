"""sat_sub — saturating subtraction, Phase 2.5.

    if (a >= b) r := a - b;
    else        r := 0;

Synthesizes `r = max(0, a - b)` using SB(n=2).

Spec:
    Pre  : true
    Post : r >= 0 and ((a >= b and r == a - b) or (a < b and r == 0))
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    template = SB(n=2),
    inputs   = [Var("a", "int", "input"), Var("b", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    pre      = "true",
    post     = ("r >= 0 and "
                "((a >= b and r == a - b) or (a < b and r == 0))"),
    atoms = {
        "g@B0.0": [
            "a >= b",                # published
            "a > b",
            "a < b",
            "a == b",
        ],
        "s@B0.0": [
            {"r": "a - b"},          # published
            {"r": "b - a"},
            {"r": "0"},
        ],
        # Phase 3.I: branch 1's explicit guard.
        "g@B0.1": [
            "a < b",                 # published — the "else"
            "a <= b",
            "a > b",
        ],
        "s@B0.1": [
            {"r": "0"},              # published
            {"r": "a - b"},
            {"r": "b - a"},
        ],
    },
    max_solutions = 5,
    expected_solutions = 3,
    expected_lean_hits = 0,
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
