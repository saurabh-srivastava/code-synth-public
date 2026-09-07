"""strategy_a_n4_prototype — Strategy A smoke test from
REPORT.md §(g).

Verifies recursive 2-way Karatsuba at n=4 over GF(2)[x] via
abstraction: polymul_2 declared as an array-valued UF with
correctness axioms; the recipe uses 3 polymul_2 calls + XOR
combining to compute polymul_4.

If the synth + Lean axiom path verifies this recipe, we've
demonstrated Strategy A working at known scale.  The next
push is n=5 with 5 polymul_2 calls or a mix of polymul_2 +
polymul_3 calls.

Counts: 3 polymul_2 calls = 3 × R(2) = 9 scalar mults total,
matching R(4) = 9 over GF(2).

The 2-way Karatsuba derivation
------------------------------
Split a(x) = a0 + a1·x + a2·x² + a3·x³  as
             a_lo(x) + a_hi(x)·x²,
where a_lo(x) = a0 + a1·x and a_hi(x) = a2 + a3·x.
Similarly b = b_lo + b_hi·x².

Then a·b = a_lo·b_lo + (a_lo·b_hi + a_hi·b_lo)·x² + a_hi·b_hi·x⁴
        = m0 + (m2 − m0 − m1)·x² + m1·x⁴

where:
    m0 = a_lo · b_lo  (= polymul_2(a0, a1, b0, b1))
    m1 = a_hi · b_hi  (= polymul_2(a2, a3, b2, b3))
    m2 = (a_lo + a_hi) · (b_lo + b_hi)
       (= polymul_2((a0+a2)%2, (a1+a3)%2,
                    (b0+b2)%2, (b1+b3)%2) over GF(2))

Each m_i is a degree-2 polynomial (3 coefficients).  The
final r0..r6 coefficients combine the m_i contributions
(over GF(2), subtraction = addition):

    r0 = m0[0]
    r1 = m0[1]
    r2 = m0[2] + m2[0] + m0[0] + m1[0]
    r3 = m2[1] + m0[1] + m1[1]
    r4 = m1[0] + m2[2] + m0[2] + m1[2]
    r5 = m1[1]
    r6 = m1[2]

Why this is a smoke test
------------------------
R(4) = 9 over GF(2) is settled (Cenk-Hasan 2007).  The
recursive Karatsuba 2-way decomposition (used by Bernstein
2009 and many crypto-block implementations) achieves it.
If our synth framework can VERIFY this recursive scheme,
the same machinery should let us VERIFY published 13-mult
algorithms at n=5 — and serve as the scaffold for
DISCOVERY work via richer predicate spaces (§G.5).
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None
# 2026-05-20: prototype.  If polymul_2 array-valued UF + GF(2)
# axioms verify, Strategy A is validated at n=4.


# UF: polymul_2 takes 4 int args (a0, a1, b0, b1) and returns
# an array-valued result holding the 3 coefficients of the
# degree-2 product polynomial (a0+a1·x)(b0+b1·x) over GF(2).
_UF = [("polymul_2", ["int", "int", "int", "int"], "int[]")]


_AXIOMS = [
    # Coefficient 0 of polymul_2(a0, a1, b0, b1) = a0 · b0.
    ("ForAll(lambda a0, a1, b0, b1: "
     " polymul_2(a0, a1, b0, b1)[0] == a0 * b0)"),
    # Coefficient 1 = (a0·b1 + a1·b0) % 2 over GF(2).
    ("ForAll(lambda a0, a1, b0, b1: "
     " polymul_2(a0, a1, b0, b1)[1] == (a0 * b1 + a1 * b0) % 2)"),
    # Coefficient 2 = a1 · b1.
    ("ForAll(lambda a0, a1, b0, b1: "
     " polymul_2(a0, a1, b0, b1)[2] == a1 * b1)"),
]


# Recipe: 3 polymul_2 calls + XOR combining.
_KARATSUBA_2WAY = [
    {"m0": "polymul_2(a0, a1, b0, b1)"},
    {"m1": "polymul_2(a2, a3, b2, b3)"},
    {"m2": "polymul_2((a0 + a2) % 2, (a1 + a3) % 2, "
                    "(b0 + b2) % 2, (b1 + b3) % 2)"},
    {"r0": "m0[0]"},
    {"r1": "m0[1]"},
    {"r2": "(m0[2] + m2[0] + m0[0] + m1[0]) % 2"},
    {"r3": "(m2[1] + m0[1] + m1[1]) % 2"},
    {"r4": "(m1[0] + m2[2] + m0[2] + m1[2]) % 2"},
    {"r5": "m1[1]"},
    {"r6": "m1[2]"},
]


# Sanity: naive 9-mult unrolled (every scalar product directly).
_NAIVE_PARALLEL = {
    "r0": "a0 * b0",
    "r1": "(a0 * b1 + a1 * b0) % 2",
    "r2": "(a0 * b2 + a1 * b1 + a2 * b0) % 2",
    "r3": "(a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) % 2",
    "r4": "(a1 * b3 + a2 * b2 + a3 * b1) % 2",
    "r5": "(a2 * b3 + a3 * b2) % 2",
    "r6": "a3 * b3",
}


PROBLEM = Problem(
    description = (
        "Compute deg-3 × deg-3 polynomial product over GF(2) "
        "via 3 recursive polymul_2 calls + XOR combining "
        "(Karatsuba 2-way split).  Demonstrates Strategy A "
        "from karatsuba_gf2/REPORT.md §(g): synth framework "
        "+ Lean axioms verify the algebraic composition."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("a0", "a1", "a2", "a3",
                          "b0", "b1", "b2", "b3")],
    outputs  = [Var(n, "int", "output")
                for n in ("r0", "r1", "r2", "r3", "r4", "r5", "r6")],
    locals   = [Var(n, "int[]", "local") for n in ("m0", "m1", "m2")],

    pre = ("0 <= a0 and a0 <= 1 and 0 <= a1 and a1 <= 1 and "
           "0 <= a2 and a2 <= 1 and 0 <= a3 and a3 <= 1 and "
           "0 <= b0 and b0 <= 1 and 0 <= b1 and b1 <= 1 and "
           "0 <= b2 and b2 <= 1 and 0 <= b3 and b3 <= 1"),
    post = ("r0 == a0 * b0 and "
            "r1 == (a0 * b1 + a1 * b0) % 2 and "
            "r2 == (a0 * b2 + a1 * b1 + a2 * b0) % 2 and "
            "r3 == (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) % 2 and "
            "r4 == (a1 * b3 + a2 * b2 + a3 * b1) % 2 and "
            "r5 == (a2 * b3 + a3 * b2) % 2 and "
            "r6 == a3 * b3"),

    uninterpreted = _UF,
    axioms = _AXIOMS,

    atoms = {
        "s@B0": [
            _KARATSUBA_2WAY,
            _NAIVE_PARALLEL,
        ],
    },
    max_solutions = 3,
    expected_solutions = None,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    print(f"strategy_a_n4_prototype — XFAIL_REASON: {XFAIL_REASON!r}")
    print(f"Goal: verify recursive 2-way Karatsuba at n=4 over GF(2)")
    print(f"      via polymul_2 UF + axioms (Strategy A smoke test).")
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
