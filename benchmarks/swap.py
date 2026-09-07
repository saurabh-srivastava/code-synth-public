"""Swap-without-temporary — POPL'10 §5.2.

Synthesize a 3-step XOR-style integer swap (using arithmetic; no extra
local var allowed).

Spec:
    Pre  : x == c1 and y == c2
    Post : x == c2 and y == c1

Template: just one `SB(n=1)`.  No loop, no proof, just a single
parallel assignment whose values are constrained by Fpre/Fpost.

Expected solution: x, y := x + y - (x + y - x), x + y - y  or some
permutation of the published three-step swap.  Phase 1.A's `SB(n=1)`
represents the entire body as a single parallel assignment, which can
satisfy `x == c2 ∧ y == c1` directly if the right atoms are present.
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    template = SB(),
    inputs   = [Var("x", "int", "input"), Var("y", "int", "input"),
                Var("c1", "int", "input"), Var("c2", "int", "input")],
    outputs  = [Var("x", "int", "output"), Var("y", "int", "output")],
    pre      = "x == c1 and y == c2",
    post     = "x == c2 and y == c1",
    atoms = {
        # Parallel assignment.  The "expected" three-step swap collapses
        # to (x, y) := (y, x) when viewed as a single transition.  The
        # interesting Phase 1.A version is to give Z3 atoms that express
        # the swap arithmetically:
        "s@B0": [
            {"x": "y", "y": "x"},                                # the obvious swap
            {"x": "x + y - x", "y": "x + y - y"},                # arithmetic identity
            {"x": "y", "y": "y"},                                # wrong
            {"x": "x", "y": "x"},                                # wrong
            {"x": "x + y - y", "y": "x + y - x"},                # same as #0 by simplification
        ],
    },
    max_solutions = 5,
    expected_solutions = 2,
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
