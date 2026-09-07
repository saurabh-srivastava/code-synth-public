"""mid3 — Phase X corpus benchmark.

Median of three scalars.  Template is `SB(n=3)` with three
disjoint guards covering all orderings.

For a, b, c, the median m is the one that's neither min nor max.

Spec:
    Pre  : true
    Post : (m == a) ∨ (m == b) ∨ (m == c) — m is one of the inputs
         ∧ at least one input is ≥ m and at least one input is ≤ m
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given three integers a, b, c, return the median — the "
        "value that is neither the maximum nor the minimum."
    ),

    template = SB(n=3),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input"),
                Var("c", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    pre      = "true",
    # m is one of the three AND at least one input is ≥ m AND
    # at least one input is ≤ m.
    post     = (
        "((m == a) or (m == b) or (m == c)) and "
        "((a >= m and (b <= m or c <= m)) or "
        " (b >= m and (a <= m or c <= m)) or "
        " (c >= m and (a <= m or b <= m)))"
    ),
    atoms = {
        # Three branches, one per "middle" pick.
        # m = a when a is between b and c.
        "g@B0.0": ["((b <= a) and (a <= c)) or ((c <= a) and (a <= b))"],
        "s@B0.0": [{"m": "a"}],
        # m = b when b is between a and c.
        "g@B0.1": ["((a <= b) and (b <= c)) or ((c <= b) and (b <= a))"],
        "s@B0.1": [{"m": "b"}],
        # m = c when c is between a and b.
        "g@B0.2": ["((a <= c) and (c <= b)) or ((b <= c) and (c <= a))"],
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
