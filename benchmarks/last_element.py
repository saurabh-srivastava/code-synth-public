"""last_element — Phase X corpus benchmark.

Return A[n - 1] when n >= 1.  Pure acyclic — one transition.
Tests the simplest possible array-read post.

Spec:
    Pre  : n >= 1
    Post : r == A[n - 1]
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length at least n (with "
        "n >= 1), return the last element A[n - 1]."
    ),

    template = SB(n=1),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    pre      = "n >= 1",
    post     = "r == A[n - 1]",
    atoms = {
        "s@B0": [{"r": "A[n - 1]"}],
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
