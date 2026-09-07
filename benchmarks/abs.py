"""abs — Phase 2.5 smoke test for SB(n=2) (conditional branches).

Synthesize the absolute-value body:

    if (x < 0) y := -x;
    else       y :=  x;

Template: `SB(n=2)` — one acyclic block with two guarded branches.
The user supplies (n−1)=1 guard candidate list; the second branch's
guard is implicit (the "else").

Spec:
    Pre  : true
    Post : y >= 0 and (y == x or y == -x)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    template = SB(n=2),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("y", "int", "output")],
    pre      = "true",
    post     = "y >= 0 and (y == x or y == 0 - x)",
    atoms = {
        # Branch 0 guard: candidates for "is x negative?"
        "g@B0.0": [
            "x < 0",                 # published
            "x <= 0",
            "x > 0",
        ],
        # Branch 0 transition: y := -x
        "s@B0.0": [
            {"y": "0 - x"},          # published
            {"y": "x"},
            {"y": "0"},
        ],
        # Phase 3.I: branch 1 is no longer an implicit "else" — it
        # needs its own guard.  Coverage `⋁ g_i ≡ true` ensures
        # together the two guards cover all of x.
        "g@B0.1": [
            "x >= 0",                # published — the "else"
            "x > 0",
            "x == 0",
        ],
        # Branch 1 transition: y := x
        "s@B0.1": [
            {"y": "x"},              # published
            {"y": "0 - x"},
            {"y": "0"},
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
