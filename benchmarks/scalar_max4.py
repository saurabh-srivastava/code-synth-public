"""scalar_max4 — Phase X corpus benchmark.

Maximum of four scalars via SB(n=4) — four branches, one per
"is the maximum" candidate.

Spec:
    Pre  : true
    Post : (m >= a) ∧ (m >= b) ∧ (m >= c) ∧ (m >= d) ∧
           ((m == a) ∨ (m == b) ∨ (m == c) ∨ (m == d))
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given four integers a, b, c, d, return the maximum of "
        "the four."
    ),

    template = SB(n=4),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input"),
                Var("c", "int", "input"),
                Var("d", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    pre      = "true",
    post     = (
        "(m >= a) and (m >= b) and (m >= c) and (m >= d) and "
        "((m == a) or (m == b) or (m == c) or (m == d))"
    ),
    atoms = {
        "g@B0.0": ["(a >= b) and (a >= c) and (a >= d)"],
        "s@B0.0": [{"m": "a"}],
        "g@B0.1": ["(b >= a) and (b >= c) and (b >= d)"],
        "s@B0.1": [{"m": "b"}],
        "g@B0.2": ["(c >= a) and (c >= b) and (c >= d)"],
        "s@B0.2": [{"m": "c"}],
        "g@B0.3": ["(d >= a) and (d >= b) and (d >= c)"],
        "s@B0.3": [{"m": "d"}],
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
