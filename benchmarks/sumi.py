"""Σ-i — compute 1+2+...+N from N using a single counter loop.

Spec: Pre `N >= 0`, Post `2*s == N*(N+1)`.

A simple loop-with-loop-invariant benchmark in the same shape as
IntSqrt.  Forward direction (not the PINS inversion). Demonstrates
that the architecture handles a different invariant / ranking shape.

Expected solution:

    SB₀ : s, i := 0, 0
    Loop guard : i < N
    SB₁ : s, i := s + i + 1, i + 1
    SB₂ : identity
    τ   : 2*s == i*(i+1) ∧ 0 <= i ∧ i <= N
    ϕ   : N - i
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("N", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "N >= 0",
    post     = "2*s == N*(N + 1)",
    atoms = {
        # Phase 2 conjunctive τ — atomic predicates.
        "tau@L0": [
            "2*s == i*(i + 1)",                                 # published #1
            "0 <= i",                                           # published #2
            "i <= N",                                           # published #3
            "s == 0",                                           # distractor
            "i == 0",                                           # distractor
        ],
        "g@L0": [
            "i < N",                                            # published
            "i <= N",
            "i > 0",
        ],
        "phi@L0": [
            "N - i",                                            # published
            "N",
            "i",
        ],
        # Entry: s, i := 0, 0
        "s@B0": [
            {"s": "0", "i": "0"},                               # published
            {"s": "1", "i": "0"},
            {"s": "0", "i": "N"},
        ],
        # Body: s, i := s + i + 1, i + 1
        "s@B1": [
            {"s": "s + i + 1", "i": "i + 1"},                   # published
            {"s": "s + i",     "i": "i + 1"},
            {"s": "s + 1",     "i": "i + 1"},
        ],
        # Exit: identity
        "s@B2": [ {} ],
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
    print(result.solutions[0].code)
