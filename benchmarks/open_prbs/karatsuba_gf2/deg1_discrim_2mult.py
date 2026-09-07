"""karatsuba_gf2_deg1_discrim_2mult — discrim test for L2.1a.

Sanity check: the framework correctly rejects 2-multiplication
candidates for degree-1 polynomial multiplication over GF(2).

The rank argument: c0 = p0*q0, c1 = p0*q1 + p1*q0, c2 = p1*q1
involve 4 bilinear product terms in p,q.  With only 2
bilinear products, we can't recover all 3 output coefficients
in general (provable via tensor rank argument).

This benchmark presents several hand-crafted 2-mult
candidates; all should UNSAT.  If any verifies, there's a
bug in the framework (most likely missing the GF(2)
boundary case).

This is NOT the L2.1b discovery target (5-mult below 6 for
n=3); it's a sanity check on the smoke-test infrastructure.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None
# 2026-05-20: all 2-mult candidates correctly rejected as
# UNSAT (rank ≥ 3 required for the bilinear form set).


# Each candidate computes only 2 multiplications, then tries
# to linearly combine them (with possible XOR sums) to
# produce r0, r1, r2.  All should be insufficient.

_CAND_P0Q0_AND_P1Q1 = [
    # m0 = p0*q0; m1 = p1*q1.  Output r1 can only be a XOR of
    # m0, m1 — no way to express p0*q1 + p1*q0.
    {"m0": "p0 * q0"},
    {"m1": "p1 * q1"},
    {"r0": "m0"},
    {"r1": "(m0 + m1) % 2"},
    {"r2": "m1"},
]


_CAND_P0Q1_AND_P1Q0 = [
    # m0 = p0*q1; m1 = p1*q0.  Output r1 = (m0+m1)%2 is
    # correct, but r0 = ?, r2 = ? — no way to express
    # p0*q0 or p1*q1.
    {"m0": "p0 * q1"},
    {"m1": "p1 * q0"},
    {"r0": "m0"},
    {"r1": "(m0 + m1) % 2"},
    {"r2": "m1"},
]


_CAND_KARATSUBA_LIKE = [
    # m0 = (p0+p1)%2 * (q0+q1)%2; m1 = p0*q0.  Try Karatsuba-
    # style but drop the m1 = p1*q1 mult.  Missing p1*q1
    # for r2.
    {"m0": "((p0 + p1) % 2) * ((q0 + q1) % 2)"},
    {"m1": "p0 * q0"},
    {"r0": "m1"},
    {"r1": "(m0 + m1) % 2"},
    {"r2": "(m0 + m1) % 2"},
]


_CAND_ALL_DIAG = [
    # m0 = p0*q0; m1 = p1*q1.  Try just diagonal terms;
    # r1 = 0 (clearly wrong unless p0*q1 + p1*q0 ≡ 0).
    {"m0": "p0 * q0"},
    {"m1": "p1 * q1"},
    {"r0": "m0"},
    {"r1": "0"},
    {"r2": "m1"},
]


PROBLEM = Problem(
    description = (
        "Discrim test: verify that 2-multiplication candidates "
        "for GF(2) degree-1 polynomial multiplication are "
        "rejected (rank ≥ 3 required for the bilinear form set)."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("p0", "p1", "q0", "q1")],
    outputs  = [Var(n, "int", "output") for n in ("r0", "r1", "r2")],
    locals   = [Var(f"m{i}", "int", "local") for i in range(2)],

    pre  = ("0 <= p0 and p0 <= 1 and "
            "0 <= p1 and p1 <= 1 and "
            "0 <= q0 and q0 <= 1 and "
            "0 <= q1 and q1 <= 1"),
    post = ("r0 == p0 * q0 and "
            "r1 == (p0 * q1 + p1 * q0) % 2 and "
            "r2 == p1 * q1"),

    atoms = {
        "s@B0": [
            _CAND_P0Q0_AND_P1Q1,
            _CAND_P0Q1_AND_P1Q0,
            _CAND_KARATSUBA_LIKE,
            _CAND_ALL_DIAG,
        ],
    },
    max_solutions = 5,
    expected_solutions = 0,  # All candidates must UNSAT.
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    print(f"karatsuba_gf2_deg1_discrim_2mult — XFAIL_REASON: {XFAIL_REASON!r}")
    result = solve(PROBLEM)
    if result:
        print(f"DISCRIM-FAIL: framework accepted a 2-mult candidate.")
        for n, sol in enumerate(result.solutions):
            print(f"── solution #{n} (score={sol.score:g}) ──")
            print(sol.code)
        raise SystemExit(1)
    print(f"DISCRIM-PASS: all 2-mult candidates UNSAT ({result.reason}).")
