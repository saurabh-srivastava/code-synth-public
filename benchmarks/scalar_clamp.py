"""scalar_clamp — Phase X corpus benchmark.

Clamp a scalar to a [lo, hi] range.  Tests SB(n=3) where the
three branches are mutually disjoint and together cover all
input cases (x < lo / lo ≤ x ≤ hi / x > hi).

Spec:
    Pre  : lo <= hi
    Post : (lo <= y <= hi)
         ∧ ((x < lo ⇒ y == lo) ∧
            (x > hi ⇒ y == hi) ∧
            (lo <= x <= hi ⇒ y == x))
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x and a range [lo, hi] (with lo ≤ hi), "
        "clamp x to the range: return lo if x < lo, hi if x > hi, "
        "otherwise x."
    ),

    template = SB(n=3),
    inputs   = [Var("x", "int", "input"),
                Var("lo", "int", "input"),
                Var("hi", "int", "input")],
    outputs  = [Var("y", "int", "output")],
    pre      = "lo <= hi",
    # Output is in [lo, hi] AND matches the clamping cases.
    post     = (
        "(lo <= y) and (y <= hi) and "
        "(((x < lo) and (y == lo)) or "
        " ((x > hi) and (y == hi)) or "
        " ((lo <= x) and (x <= hi) and (y == x)))"
    ),
    atoms = {
        "g@B0.0": ["x < lo"],
        "s@B0.0": [{"y": "lo"}],
        "g@B0.1": ["x > hi"],
        "s@B0.1": [{"y": "hi"}],
        "g@B0.2": ["(lo <= x) and (x <= hi)"],
        "s@B0.2": [{"y": "x"}],
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
