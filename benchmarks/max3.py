"""max3 — Phase X corpus benchmark.

Three-way maximum: return the largest of three scalar inputs.
Template is `SB(n=3)` — three guarded branches in an acyclic
block.  Tests N-way conditional dispatch beyond the 2-way pattern
exercised by `abs.py` / `sat_sub.py`.

Spec:
    Pre  : true
    Post : (m >= a) ∧ (m >= b) ∧ (m >= c) ∧
           ((m == a) ∨ (m == b) ∨ (m == c))
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given three integers a, b, c, return the maximum of the "
        "three."
    ),

    template = SB(n=3),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input"),
                Var("c", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    pre      = "true",
    post     = ("(m >= a) and (m >= b) and (m >= c) and "
                "((m == a) or (m == b) or (m == c))"),
    atoms = {
        # Branch 0: a is the max.
        "g@B0.0": ["(a >= b) and (a >= c)"],
        "s@B0.0": [{"m": "a"}],
        # Branch 1: b is the max.
        "g@B0.1": ["(b >= a) and (b >= c)"],
        "s@B0.1": [{"m": "b"}],
        # Branch 2: c is the max.
        "g@B0.2": ["(c >= a) and (c >= b)"],
        "s@B0.2": [{"m": "c"}],
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
