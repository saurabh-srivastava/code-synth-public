"""saturate_add — Phase X corpus benchmark.

Saturating addition: compute `a + b` but clamp the result to
`[LO, HI]`.  Three-way SB(n=3) on whether the sum falls below,
within, or above the range.

Spec:
    Pre  : LO <= HI
    Post : (LO <= y <= HI)
         ∧ ((a + b < LO ⇒ y == LO) ∧
            (a + b > HI ⇒ y == HI) ∧
            (LO <= a + b <= HI ⇒ y == a + b))
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given integers a, b, LO, HI (with LO <= HI), compute "
        "saturating addition: return a + b clamped to [LO, HI]. "
        "If a + b < LO, return LO; if a + b > HI, return HI; "
        "otherwise return a + b."
    ),

    template = SB(n=3),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input"),
                Var("LO", "int", "input"),
                Var("HI", "int", "input")],
    outputs  = [Var("y", "int", "output")],
    pre      = "LO <= HI",
    post     = (
        "(LO <= y) and (y <= HI) and "
        "(((a + b < LO) and (y == LO)) or "
        " ((a + b > HI) and (y == HI)) or "
        " ((LO <= a + b) and (a + b <= HI) and (y == a + b)))"
    ),
    atoms = {
        "g@B0.0": ["a + b < LO"],
        "s@B0.0": [{"y": "LO"}],
        "g@B0.1": ["a + b > HI"],
        "s@B0.1": [{"y": "HI"}],
        "g@B0.2": ["(LO <= a + b) and (a + b <= HI)"],
        "s@B0.2": [{"y": "a + b"}],
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
