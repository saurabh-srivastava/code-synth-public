"""karatsuba_gf2_deg2_discrim_5mult — sanity discrim for L2.1b.

Sanity check: hand-crafted 5-multiplication candidates for
degree-2 polynomial multiplication over GF(2) should all be
UNSAT under the conjecture that 6 is the optimal multiplication
count.

This is NOT the full L2.1b discovery target.  A complete search
over 5-multiplication algorithms requires §G.5's parametric m_i
template — bilinear-form holes with coefficient holes from
`{0, 1}` enumerated across all 16⁵ ≈ 1M combinations (modulo
symmetries).  This file demonstrates the framework correctly
rejects a few hand-picked 5-mult attempts.

The conjecture
--------------
For polynomial multiplication of two degree-2 polynomials over
GF(2)[x], the best known is 6 multiplications (Karatsuba-style
with mult-sharing between the (α·β) and ((α+p2)·(β+q2))
sub-products).  Whether 5 is achievable is **open**.

A genuine 5-mult algorithm would be a publishable result: it
would beat the current best for GF(2) polynomial multiplication
at degree 2, with crypto-relevant implications (faster GHASH,
AES-GCM block multiplication).

The candidates here
-------------------
Each candidate has 5 explicit multiplications.  The output
coefficients are constrained to be linear combinations (over
GF(2)) of the 5 products.  Without the parametric m_i template,
we can only check a finite set of hand-crafted candidates.

Each tries to drop ONE of the 6 Karatsuba mults and substitute
with a different bilinear form OR a no-mult linear combination
of the remaining 5.  All should UNSAT.

If any verifies, either:
  (a) Our 6-mult Karatsuba was not minimal — the open question
      is partly answered in the affirmative.
  (b) There's a soundness bug in the framework.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None
# 2026-05-20: all 5-mult candidates correctly UNSAT.


# Candidate 1: drop m2 (p2·q2); try to derive r4 from the
# other 5 mults via Karatsuba relations.
# We'd want r4 = p2·q2 = m1a + m0a + (p0·q2 + p2·q0).  But
# we don't have (p0·q2 + p2·q0) without an extra mult.
_CAND_DROP_M2 = [
    {"m0a": "p0 * q0"},
    {"m0c": "((p0 + p1) % 2) * ((q0 + q1) % 2)"},
    {"m1":  "p1 * q1"},
    {"m1a": "((p0 + p2) % 2) * ((q0 + q2) % 2)"},
    {"m1c": "((p0 + p1 + p2) % 2) * ((q0 + q1 + q2) % 2)"},
    {"r0":  "m0a"},
    {"r1":  "(m0c + m0a + m1) % 2"},
    {"r2":  "(m1a + m0a + m1) % 2"},
    {"r3":  "(m1c + m0c + m1a + m0a) % 2"},
    {"r4":  "(m1a + m0a) % 2"},   # WRONG — needs p2*q2.
]


# Candidate 2: drop m1 (p1·q1); try to derive its uses via the
# other 5 mults.  The output formulas reference m1 in r1 and r2.
_CAND_DROP_M1 = [
    {"m0a": "p0 * q0"},
    {"m0c": "((p0 + p1) % 2) * ((q0 + q1) % 2)"},
    {"m1a": "((p0 + p2) % 2) * ((q0 + q2) % 2)"},
    {"m1c": "((p0 + p1 + p2) % 2) * ((q0 + q1 + q2) % 2)"},
    {"m2":  "p2 * q2"},
    {"r0":  "m0a"},
    {"r1":  "(m0c + m0a) % 2"},   # WRONG — m1 missing.
    {"r2":  "(m1a + m0a + m2) % 2"},
    {"r3":  "(m1c + m0c + m1a + m0a) % 2"},
    {"r4":  "m2"},
]


# Candidate 3: drop m0c; try to derive its uses via the other
# 5 mults.
_CAND_DROP_M0C = [
    {"m0a": "p0 * q0"},
    {"m1":  "p1 * q1"},
    {"m1a": "((p0 + p2) % 2) * ((q0 + q2) % 2)"},
    {"m1c": "((p0 + p1 + p2) % 2) * ((q0 + q1 + q2) % 2)"},
    {"m2":  "p2 * q2"},
    {"r0":  "m0a"},
    {"r1":  "(m0a + m1) % 2"},   # WRONG — m0c missing.
    {"r2":  "(m1a + m0a + m2 + m1) % 2"},
    {"r3":  "(m1c + m1a + m0a) % 2"},
    {"r4":  "m2"},
]


# Candidate 4: use a different set of 5 bilinear forms entirely.
# A "non-Karatsuba" 5-mult attempt.
_CAND_ALT_5 = [
    {"n0": "p0 * q0"},
    {"n1": "p1 * q1"},
    {"n2": "p2 * q2"},
    {"n3": "((p0 + p1 + p2) % 2) * ((q0 + q1 + q2) % 2)"},
    {"n4": "((p0 + p2) % 2) * ((q1) % 2)"},
    {"r0": "n0"},
    {"r1": "(n3 + n0 + n1 + n2 + n4) % 2"},
    {"r2": "(n4 + n1) % 2"},
    {"r3": "(n3 + n0 + n1 + n2 + n4) % 2"},
    {"r4": "n2"},
]


# Note: candidates 1-4 use different local variable names but
# the synthesizer's local declaration list must accommodate ALL
# of them.  Below we declare a superset (m0a, m0c, m1, m1a, m1c,
# n0..n4) so each candidate parses cleanly.
_ALL_LOCALS = ["m0a", "m0c", "m1", "m1a", "m1c", "m2",
               "n0", "n1", "n2", "n3", "n4"]


PROBLEM = Problem(
    description = (
        "Discrim test: hand-crafted 5-multiplication candidates "
        "for GF(2) degree-2 polynomial multiplication should all "
        "be UNSAT under the conjecture that 6 is optimal."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("p0", "p1", "p2", "q0", "q1", "q2")],
    outputs  = [Var(n, "int", "output")
                for n in ("r0", "r1", "r2", "r3", "r4")],
    locals   = [Var(n, "int", "local") for n in _ALL_LOCALS],

    pre  = ("0 <= p0 and p0 <= 1 and "
            "0 <= p1 and p1 <= 1 and "
            "0 <= p2 and p2 <= 1 and "
            "0 <= q0 and q0 <= 1 and "
            "0 <= q1 and q1 <= 1 and "
            "0 <= q2 and q2 <= 1"),
    post = ("r0 == p0 * q0 and "
            "r1 == (p0 * q1 + p1 * q0) % 2 and "
            "r2 == (p0 * q2 + p1 * q1 + p2 * q0) % 2 and "
            "r3 == (p1 * q2 + p2 * q1) % 2 and "
            "r4 == p2 * q2"),

    atoms = {
        "s@B0": [
            _CAND_DROP_M2,
            _CAND_DROP_M1,
            _CAND_DROP_M0C,
            _CAND_ALT_5,
        ],
    },
    max_solutions = 5,
    expected_solutions = 0,  # All must UNSAT.
    solver_timeout_ms = 900_000,
)


if __name__ == "__main__":
    print(f"karatsuba_gf2_deg2_discrim_5mult — XFAIL_REASON: {XFAIL_REASON!r}")
    result = solve(PROBLEM)
    if result:
        print(f"DISCRIM-FAIL: framework accepted a 5-mult candidate!")
        print(f"This may be a real result — investigate.")
        for n, sol in enumerate(result.solutions):
            print(f"── solution #{n} (score={sol.score:g}) ──")
            print(sol.code)
        raise SystemExit(1)
    print(f"DISCRIM-PASS: all 5-mult candidates UNSAT ({result.reason}).")
