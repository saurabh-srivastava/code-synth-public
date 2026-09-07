"""Diagnostic 3: full n=5 Karatsuba with ground axioms.

Same recipe as strategy_a_n5_2way_prototype but with GROUND
axioms (specific to the recipe's polymul_3 / polymul_2 call
arguments) instead of universal axioms.  This bypasses Z3's
quantifier instantiation, which is the suspected culprit.

If this verifies, the issue in strategy_a_n5_2way_prototype
is universal-axiom E-matching at scale.  Fix: per-recipe
ground axioms, OR add explicit Z3 patterns / triggers.
"""
from synth import Problem, SB, Var, solve


_UF = [
    ("polymul_3", ["int", "int", "int", "int", "int", "int"], "int[]"),
    ("polymul_2", ["int", "int", "int", "int"], "int[]"),
]


# GROUND axioms: instantiate polymul_3 / polymul_2 at the
# specific arguments the recipe uses.  No quantifiers.
_AXIOMS = [
    # m_lo = polymul_3(a0, a1, a2, b0, b1, b2) coefficients.
    "polymul_3(a0, a1, a2, b0, b1, b2)[0] == a0 * b0",
    "polymul_3(a0, a1, a2, b0, b1, b2)[1] == (a0 * b1 + a1 * b0) % 2",
    "polymul_3(a0, a1, a2, b0, b1, b2)[2] == (a0 * b2 + a1 * b1 + a2 * b0) % 2",
    "polymul_3(a0, a1, a2, b0, b1, b2)[3] == (a1 * b2 + a2 * b1) % 2",
    "polymul_3(a0, a1, a2, b0, b1, b2)[4] == a2 * b2",
    # m_hi = polymul_2(a3, a4, b3, b4) coefficients.
    "polymul_2(a3, a4, b3, b4)[0] == a3 * b3",
    "polymul_2(a3, a4, b3, b4)[1] == (a3 * b4 + a4 * b3) % 2",
    "polymul_2(a3, a4, b3, b4)[2] == a4 * b4",
    # m_mix = polymul_3((a0+a3)%2, (a1+a4)%2, a2, (b0+b3)%2, (b1+b4)%2, b2) coeffs.
    # We use the synthesized intermediates s_a0, s_a1, s_b0, s_b1.
    "polymul_3((a0+a3)%2, (a1+a4)%2, a2, (b0+b3)%2, (b1+b4)%2, b2)[0] == "
    "  ((a0+a3)%2) * ((b0+b3)%2)",
    "polymul_3((a0+a3)%2, (a1+a4)%2, a2, (b0+b3)%2, (b1+b4)%2, b2)[1] == "
    "  (((a0+a3)%2) * ((b1+b4)%2) + ((a1+a4)%2) * ((b0+b3)%2)) % 2",
    "polymul_3((a0+a3)%2, (a1+a4)%2, a2, (b0+b3)%2, (b1+b4)%2, b2)[2] == "
    "  (((a0+a3)%2) * b2 + ((a1+a4)%2) * ((b1+b4)%2) + a2 * ((b0+b3)%2)) % 2",
    "polymul_3((a0+a3)%2, (a1+a4)%2, a2, (b0+b3)%2, (b1+b4)%2, b2)[3] == "
    "  (((a1+a4)%2) * b2 + a2 * ((b1+b4)%2)) % 2",
    "polymul_3((a0+a3)%2, (a1+a4)%2, a2, (b0+b3)%2, (b1+b4)%2, b2)[4] == "
    "  a2 * b2",
]


_KARATSUBA = [
    {"m_lo":  "polymul_3(a0, a1, a2, b0, b1, b2)"},
    {"m_hi":  "polymul_2(a3, a4, b3, b4)"},
    {"m_mix": "polymul_3((a0 + a3) % 2, (a1 + a4) % 2, a2, "
                       "(b0 + b3) % 2, (b1 + b4) % 2, b2)"},
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


PROBLEM = Problem(
    description = "Diagnostic 3: full n=5 Karatsuba with ground axioms.",
    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("a0", "a1", "a2", "a3", "a4",
                          "b0", "b1", "b2", "b3", "b4")],
    outputs  = [Var(n, "int", "output")
                for n in ("r0", "r1", "r2", "r3", "r4",
                          "r5", "r6", "r7", "r8")],
    locals   = [Var(n, "int[]", "local") for n in ("m_lo", "m_hi", "m_mix")],
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
    atoms = {"s@B0": [_KARATSUBA]},
    max_solutions = 2,
    expected_solutions = None,
    solver_timeout_ms = 1_200_000,
)


if __name__ == "__main__":
    print("Diagnostic 3: full n=5 Karatsuba with GROUND axioms.")
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
    else:
        print(f"Found {len(result.solutions)} solution(s).")
        for n, sol in enumerate(result.solutions):
            print(f"── solution #{n} (score={sol.score:g}) ──")
            print(sol.code)
