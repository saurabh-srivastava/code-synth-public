"""Multiplication via repeated addition — Phase 2 conjunctive τ demo.

Compute p = a*b using only addition and a counter loop.

    p, i := 0, 0;
    while (i < b)
        p, i := p + a, i + 1;

The natural invariant is the conjunction `p == a*i ∧ 0 ≤ i ∧ i ≤ b`,
made of three atomic predicates.  Phase 2's conjunctive dispatch picks
the right subset from a candidate pool that includes distractors.

Spec:
    Pre  : a >= 0 and b >= 0
    Post : p == a*b
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("a", "int", "input"), Var("b", "int", "input")],
    outputs  = [Var("p", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "a >= 0 and b >= 0",
    post     = "p == a*b",
    atoms = {
        # Conjunctive τ — Z3 selects a subset.  The published τ is
        # the conjunction of atoms 0, 1, 2.
        "tau@L0": [
            "p == a*i",                                         # published #1
            "0 <= i",                                           # published #2
            "i <= b",                                           # published #3
            "p >= 0",                                           # redundant but valid
            "a == b",                                           # wrong (over-constrains)
            "p == 0",                                           # wrong
        ],
        "g@L0":  ["i < b", "i <= b", "i > 0"],
        "phi@L0": ["b - i", "b", "i"],
        # Entry: p, i := 0, 0
        "s@B0": [
            {"p": "0", "i": "0"},                               # published
            {"p": "a", "i": "0"},
            {"p": "0", "i": "1"},
        ],
        # Body: p, i := p + a, i + 1
        "s@B1": [
            {"p": "p + a", "i": "i + 1"},                       # published
            {"p": "p + 1", "i": "i + 1"},
            {"p": "p + b", "i": "i + 1"},
        ],
        # Exit: identity
        "s@B2": [ {} ],
    },
    max_solutions = 8,
    expected_solutions = 4,  # 2 -> 4 after Phase Fpre-Sym (2026-06-08):
                              # τ atoms `0 <= i` and `p >= 0` are now
                              # provably preserved when Fpre's input
                              # facts propagate into the inductive
                              # antecedent.  Sound additions.
    expected_lean_hits = 0,
    solver_timeout_ms = 120_000,
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
