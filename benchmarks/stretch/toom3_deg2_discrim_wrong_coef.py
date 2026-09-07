"""toom3_deg2_discrim_wrong_coef — discrimination test.

DELIBERATELY INVALID PROBLEM.  The Toom-3 interpolation steps
use rational coefficients (1/2 and 1/6) that are exact under
the polynomial identity.  This benchmark substitutes a WRONG
denominator (// 3 instead of // 2 for the r2 step) to verify
the synthesizer notices.

If this test ever PASSES synthesis, it indicates that the
verifier accepted a structurally-wrong arithmetic chain — most
likely a regression where integer division semantics or
polynomial expansion isn't being checked tightly.

Companion to `toom3_deg2.py` (positive test).
"""
from synth import Problem, SB, Var


EXPECT_NO_SOLUTION = True


# Single deliberately-wrong candidate: r2 uses // 3 instead of // 2.
_WRONG_TOOM3 = [
    {"m0": "p0 * q0"},
    {"m1": "(p0 + p1 + p2) * (q0 + q1 + q2)"},
    {"m2": "(p0 - p1 + p2) * (q0 - q1 + q2)"},
    {"m3": "(p0 + 2*p1 + 4*p2) * (q0 + 2*q1 + 4*q2)"},
    {"m4": "p2 * q2"},
    {"r0": "m0"},
    {"r4": "m4"},
    # WRONG: should be // 2.  (m1 + m2) IS divisible by 2 but NOT
    # always by 3, so this is a genuine arithmetic error.
    {"r2": "(m1 + m2) // 3 - m0 - m4"},
    {"r3": "(m3 + 3*m0 - 3*m1 - m2 - 12*m4) // 6"},
    {"r1": "(m1 - m2) // 2 - r3"},
]


PROBLEM = Problem(
    description = (
        "DISCRIMINATION TEST — must return NoSolution.  Toom-3 "
        "deg-2 × deg-2 polynomial product with a wrong "
        "interpolation coefficient (// 3 instead of // 2)."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("p0", "p1", "p2", "q0", "q1", "q2")],
    outputs  = [Var(f"r{i}", "int", "output") for i in range(5)],
    locals   = [Var(f"m{i}", "int", "local") for i in range(5)],

    pre  = "true",
    post = ("r0 == p0 * q0 and "
            "r1 == p0 * q1 + p1 * q0 and "
            "r2 == p0 * q2 + p1 * q1 + p2 * q0 and "
            "r3 == p1 * q2 + p2 * q1 and "
            "r4 == p2 * q2"),

    atoms = {"s@B0": [_WRONG_TOOM3]},
    max_solutions = 1,
    solver_timeout_ms = 120_000,
)


if __name__ == "__main__":
    from synth import solve
    result = solve(PROBLEM)
    if result:
        print(f"DISCRIM-FAIL: {len(result.solutions)} verified!")
        raise SystemExit(1)
    print(f"DISCRIM-PASS: rejected ({result.reason})")
