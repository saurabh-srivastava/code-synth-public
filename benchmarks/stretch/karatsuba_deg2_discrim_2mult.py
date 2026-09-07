"""karatsuba_deg2_discrim_2mult — discrimination test.

DELIBERATELY INVALID PROBLEM.  All candidates use only TWO scalar
multiplications, which is provably insufficient for computing
the degree-1 × degree-1 polynomial product (tensor-rank lower
bound is 3; Karatsuba achieves it).  The synthesizer MUST
reject all candidates — `NoSolution` is the passing outcome.

This is a regression guard against the synthesizer accidentally
accepting an unsound candidate.  If this test ever PASSES
synthesis (i.e., returns SolveResult), it indicates a soundness
regression — verify the encoding, the lenient-fallback escape
hatch, and the per-class UNKNOWN handling.

Companion to `karatsuba_deg2.py` (positive test).
"""
from synth import Problem, SB, Var


EXPECT_NO_SOLUTION = True


# Four representative 2-mult candidates, Karatsuba-shaped but
# missing one of the three multiplications.
_CANDIDATES = [
    # Drop m1 (p1*q1): can't produce r2.
    [
        {"m0": "p0 * q0"},
        {"m1": "(p0 + p1) * (q0 + q1)"},
        {"r0": "m0"},
        {"r1": "m1 - m0"},
        {"r2": "0"},
    ],
    # Drop m0 (p0*q0): can't produce r0.
    [
        {"m0": "(p0 + p1) * (q0 + q1)"},
        {"m1": "p1 * q1"},
        {"r0": "0"},
        {"r1": "m0 - m1"},
        {"r2": "m1"},
    ],
    # Diagonal only: can't produce r1.
    [
        {"m0": "p0 * q0"},
        {"m1": "p1 * q1"},
        {"r0": "m0"},
        {"r1": "0"},
        {"r2": "m1"},
    ],
    # Sum/diff: each output coalesces — none recover the three coefs.
    [
        {"m0": "(p0 + p1) * (q0 + q1)"},
        {"m1": "(p0 - p1) * (q0 - q1)"},
        {"r0": "m0 + m1"},
        {"r1": "m0 - m1"},
        {"r2": "m0 + m1"},
    ],
]


PROBLEM = Problem(
    description = (
        "DISCRIMINATION TEST — must return NoSolution.  Four 2-mult "
        "Karatsuba-shaped candidates for degree-1 polynomial product; "
        "tensor rank says 3 multiplications are required, so all "
        "candidates are invalid."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("p0", "p1", "q0", "q1")],
    outputs  = [Var(n, "int", "output") for n in ("r0", "r1", "r2")],
    locals   = [Var(f"m{i}", "int", "local") for i in range(2)],

    pre  = "true",
    post = ("r0 == p0 * q0 and "
            "r1 == p0 * q1 + p1 * q0 and "
            "r2 == p1 * q1"),

    atoms = {"s@B0": _CANDIDATES},
    max_solutions = 1,
    solver_timeout_ms = 120_000,
)


if __name__ == "__main__":
    from synth import solve
    result = solve(PROBLEM)
    if result:
        print(f"DISCRIM-FAIL: {len(result.solutions)} candidate(s) verified!")
        raise SystemExit(1)
    print(f"DISCRIM-PASS: all rejected ({result.reason})")
