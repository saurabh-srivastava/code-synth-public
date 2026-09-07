"""strategy_a_n5_2way_prototype — Strategy A at n=5.

Verifies recursive 2-way Karatsuba at n=5 over GF(2)[x] via
abstraction: polymul_2 + polymul_3 declared as array-valued
UFs with correctness axioms; the recipe uses 2 polymul_3
calls + 1 polymul_2 call + XOR combining to compute polymul_5.

At n=5, the natural Karatsuba split is n=3+2 (unequal):
    a = a_lo(x) + a_hi(x)·x³
        where a_lo = a0 + a1·x + a2·x² (deg-2, 3 coeffs)
              a_hi = a3 + a4·x         (deg-1, 2 coeffs)
    b = b_lo(x) + b_hi(x)·x³  (analogously)

Then a·b = m_lo + (m_mix − m_lo − m_hi)·x³ + m_hi·x⁶
        = m_lo + m_mid·x³ + m_hi·x⁶  (m_mid via XOR over GF(2))

where:
    m_lo  = a_lo · b_lo  (deg-4, polymul_3 call)
    m_hi  = a_hi · b_hi  (deg-2, polymul_2 call)
    m_mix = (a_lo+a_hi) · (b_lo+b_hi)  (deg-4, polymul_3 call)

Total abstract mults: 2 × polymul_3 + 1 × polymul_2.
At the SCALAR level (using R(2)=3, R(3)=6):
    2·R(3) + R(2) = 2·6 + 3 = **15 scalar mults**.

This is suboptimal vs Cenk-Hasan's R(5) ≤ 13 (which uses a
specific non-Karatsuba interpolation).  But 15 demonstrates
Strategy A scales TO n=5; the 13-mult discovery is a follow-up
that needs a richer predicate space (§G.5 parametric m_i over
interpolation matrices, per REPORT.md §(g) Strategy B).

Coefficient derivation (over GF(2))
-----------------------------------
With m_lo (deg-4, positions 0..4), m_hi (deg-2, positions 0..2),
m_mix (deg-4, positions 0..4); m_mid[k] = m_mix[k] + m_lo[k]
+ (m_hi[k] if k≤2 else 0) for k = 0..4:

    r0 = m_lo[0]
    r1 = m_lo[1]
    r2 = m_lo[2]
    r3 = m_lo[3] + m_mid[0]   = m_lo[3] + m_mix[0] + m_lo[0] + m_hi[0]
    r4 = m_lo[4] + m_mid[1]   = m_lo[4] + m_mix[1] + m_lo[1] + m_hi[1]
    r5 = m_mid[2]             = m_mix[2] + m_lo[2] + m_hi[2]
    r6 = m_mid[3] + m_hi[0]   = m_mix[3] + m_lo[3] + m_hi[0]
    r7 = m_mid[4] + m_hi[1]   = m_mix[4] + m_lo[4] + m_hi[1]
    r8 = m_hi[2]

All sums over GF(2) (modulo 2).
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None
# 2026-05-20: Strategy A pushed to n=5 with 2-way 3+2 split.


# UF: polymul_3 returns a 5-coefficient deg-4 polynomial
# (degree-2 × degree-2 product).
# UF: polymul_2 returns a 3-coefficient deg-2 polynomial.
_UF = [
    ("polymul_3", ["int", "int", "int", "int", "int", "int"], "int[]"),
    ("polymul_2", ["int", "int", "int", "int"], "int[]"),
]

_AXIOMS = [
    # polymul_3 coefficients (over GF(2)).
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[0] == a0 * b0)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[1] == (a0 * b1 + a1 * b0) % 2)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[2] == "
     "  (a0 * b2 + a1 * b1 + a2 * b0) % 2)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[3] == (a1 * b2 + a2 * b1) % 2)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[4] == a2 * b2)"),
    # polymul_2 coefficients.
    ("ForAll(lambda a0, a1, b0, b1: "
     " polymul_2(a0, a1, b0, b1)[0] == a0 * b0)"),
    ("ForAll(lambda a0, a1, b0, b1: "
     " polymul_2(a0, a1, b0, b1)[1] == (a0 * b1 + a1 * b0) % 2)"),
    ("ForAll(lambda a0, a1, b0, b1: "
     " polymul_2(a0, a1, b0, b1)[2] == a1 * b1)"),
]


# Recipe: 2 polymul_3 + 1 polymul_2 + XOR combining.
# Split the GF(2)-XORed args for m_mix into named locals so the
# polymul_3 axiom E-matches cleanly against variable patterns
# (Z3 / Lean handle Variable args more reliably than computed
# expressions when matching quantified UF axioms).
_KARATSUBA_2WAY_3_PLUS_2 = [
    {"s_a0":  "(a0 + a3) % 2"},
    {"s_a1":  "(a1 + a4) % 2"},
    {"s_b0":  "(b0 + b3) % 2"},
    {"s_b1":  "(b1 + b4) % 2"},
    # m_lo = a_lo · b_lo  via polymul_3.
    {"m_lo":  "polymul_3(a0, a1, a2, b0, b1, b2)"},
    # m_hi = a_hi · b_hi  via polymul_2.
    {"m_hi":  "polymul_2(a3, a4, b3, b4)"},
    # m_mix = (a_lo + a_hi) · (b_lo + b_hi) via polymul_3.
    # a_lo + a_hi = (s_a0, s_a1, a2) over GF(2) (a_hi has no
    # x²-coefficient, so the x² stays a2).
    {"m_mix": "polymul_3(s_a0, s_a1, a2, s_b0, s_b1, b2)"},
    # Output coefficients.
    {"r0": "m_lo[0]"},
    {"r1": "m_lo[1]"},
    {"r2": "m_lo[2]"},
    {"r3": "(m_lo[3] + m_mix[0] + m_lo[0] + m_hi[0]) % 2"},
    {"r4": "(m_lo[4] + m_mix[1] + m_lo[1] + m_hi[1]) % 2"},
    {"r5": "(m_mix[2] + m_lo[2] + m_hi[2]) % 2"},
    {"r6": "(m_mix[3] + m_lo[3] + m_hi[0]) % 2"},
    {"r7": "(m_mix[4] + m_lo[4] + m_hi[1]) % 2"},
    {"r8": "m_hi[2]"},
]


# Naive 25-mult (baseline).
_NAIVE_PARALLEL = {
    "r0": "a0 * b0",
    "r1": "(a0 * b1 + a1 * b0) % 2",
    "r2": "(a0 * b2 + a1 * b1 + a2 * b0) % 2",
    "r3": "(a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) % 2",
    "r4": "(a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) % 2",
    "r5": "(a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) % 2",
    "r6": "(a2 * b4 + a3 * b3 + a4 * b2) % 2",
    "r7": "(a3 * b4 + a4 * b3) % 2",
    "r8": "a4 * b4",
}


PROBLEM = Problem(
    description = (
        "Compute deg-4 × deg-4 polynomial product over GF(2) "
        "via recursive 2-way Karatsuba (3+2 unequal split) "
        "using 1 polymul_2 + 2 polymul_3 calls + XOR "
        "combining.  Strategy A from REPORT.md §(g) extended "
        "to n=5."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("a0", "a1", "a2", "a3", "a4",
                          "b0", "b1", "b2", "b3", "b4")],
    outputs  = [Var(n, "int", "output")
                for n in ("r0", "r1", "r2", "r3", "r4",
                          "r5", "r6", "r7", "r8")],
    locals   = ([Var(n, "int", "local")
                 for n in ("s_a0", "s_a1", "s_b0", "s_b1")]
                + [Var(n, "int[]", "local")
                   for n in ("m_lo", "m_hi", "m_mix")]),

    pre = (" and ".join(f"0 <= {v} and {v} <= 1"
                        for v in ("a0", "a1", "a2", "a3", "a4",
                                  "b0", "b1", "b2", "b3", "b4"))),
    post = (
        "r0 == a0 * b0 and "
        "r1 == (a0 * b1 + a1 * b0) % 2 and "
        "r2 == (a0 * b2 + a1 * b1 + a2 * b0) % 2 and "
        "r3 == (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) % 2 and "
        "r4 == (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) % 2 and "
        "r5 == (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) % 2 and "
        "r6 == (a2 * b4 + a3 * b3 + a4 * b2) % 2 and "
        "r7 == (a3 * b4 + a4 * b3) % 2 and "
        "r8 == a4 * b4"
    ),

    uninterpreted = _UF,
    axioms = _AXIOMS,

    atoms = {
        "s@B0": [
            _KARATSUBA_2WAY_3_PLUS_2,
            _NAIVE_PARALLEL,
        ],
    },
    max_solutions = 3,
    expected_solutions = None,
    solver_timeout_ms = 1_800_000,  # 30 min budget.
)


if __name__ == "__main__":
    # The per-class Z3 timeout (default 10s) is too short for
    # this benchmark's quantifier instantiation work — Z3 needs
    # to apply polymul_3/polymul_2 axioms at multiple call sites
    # and combine them with the XOR-mod-2 combining formulas.
    # Bumping to 5 min per check enables verification.
    #
    # Future: surface as a Problem field per_check_timeout_ms.
    import synth.solver
    synth.solver._PER_CHECK_TIMEOUT_MS = 300_000  # 5 min per check

    print(f"strategy_a_n5_2way_prototype — XFAIL_REASON: {XFAIL_REASON!r}")
    print(f"Goal: verify recursive 2-way Karatsuba at n=5 over GF(2)")
    print(f"      via 1 polymul_2 + 2 polymul_3 UF calls + XOR")
    print(f"      combining (Strategy A pushed to n=5).")
    print(f"Expected: 15 scalar mults (vs 25 naive, vs 13 Cenk-Hasan optimal).")
    print(f"Per-class Z3 timeout: "
          f"{synth.solver._PER_CHECK_TIMEOUT_MS / 1000:.0f}s (bumped).")
    print()
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1 if XFAIL_REASON is None else 0)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
