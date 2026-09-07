"""IntSqrt — POPL'10 Example 1, re-stated against the synth package.

This is the same benchmark as the phase 0 spike (since removed) but expressed through
the production Problem + eDSL + solver pipeline.  Used as the Phase 1
smoke test.

Expected output (POPL'10 Eq. (7)):

    τ   :  v == i*i  ∧  x >= (i-1)*(i-1)  ∧  i >= 1
    g₀  :  v <= x
    ϕ   :  x - (i-1)*(i-1)
    s₁  :  v' = 1, i' = 1                       (x preserved)
    s₂  :  v' = v + 2*i + 1, i' = i + 1         (x preserved)
    s₃  :  identity                              (everything preserved)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("i", "int", "output")],
    locals   = [Var("v", "int", "local")],
    pre      = "x >= 1",
    post     = "(i - 1)*(i - 1) <= x and x < i*i",
    atoms = {
        # Loop L0.
        # τ uses Phase 2's conjunctive dispatch — atomic predicates that
        # the solver combines.  The published τ from POPL'10 Eq. (7) is
        # the conjunction of atoms 0, 1, 2.
        "tau@L0": [
            "v == i*i",                                        # published #1
            "x >= (i - 1)*(i - 1)",                            # published #2
            "i >= 1",                                          # published #3
            "v >= x",                                          # distractor
            "i == 1",                                          # distractor
        ],
        "g@L0": [
            "v <= x",                                          # published
            "v <  x",
            "i <= x",
        ],
        "phi@L0": [
            "x - (i - 1)*(i - 1)",                             # published
            "x - i",
            "x",
        ],

        # SB B0 — entry.  Each atom is {output_var: rhs_expr}; vars not
        # listed are preserved (x' = x).
        "s@B0": [
            {"v": "1", "i": "1"},                              # published
            {"v": "0", "i": "0"},
            {"v": "x", "i": "1"},
        ],

        # SB B1 — loop body.
        "s@B1": [
            {"v": "v + 2*i + 1", "i": "i + 1"},                # published
            {"v": "v + i",       "i": "i + 1"},
            {"v": "v + 2",       "i": "i + 1"},
        ],

        # SB B2 — exit (identity = empty dict).
        "s@B2": [
            {},                                                # published (identity)
        ],
    },
    max_solutions = 5,
    expected_solutions = 1,
    expected_lean_hits = 0,
)


if __name__ == "__main__":
    result = solve(PROBLEM)

    if not result:
        # NoSolution or Timeout.
        print(f"FAILED: {result.reason}")
        if hasattr(result, "hints"):
            for h in result.hints:
                print(f"  hint: {h}")
        raise SystemExit(1)

    print(f"Found {len(result.solutions)} solution(s).")
    for n, sol in enumerate(result.solutions):
        print()
        print(f"── solution #{n}  (score={sol.score:g}, "
              f"breakdown={sol.score_components}) ──")
        print(sol.code)
        print()
        print("  choices:")
        for hid, k in sorted(sol.choices.items()):
            print(f"    {hid:10s}  →  [#{k}]  {sol.atoms[hid]!r}")
