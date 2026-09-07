"""toom3_deg2 — Phase X.S stretch corpus (edge of open).

Multiply two degree-2 polynomials
    P = p0 + p1·x + p2·x²
    Q = q0 + q1·x + q2·x²
yielding their degree-4 product
    R = r0 + r1·x + r2·x² + r3·x³ + r4·x⁴

using only 5 scalar multiplications (Toom-Cook 3-way, "Toom-3")
instead of the naive 9.

Spec:
    Pre  : true
    Post : r0 == p0*q0
         ∧ r1 == p0*q1 + p1*q0
         ∧ r2 == p0*q2 + p1*q1 + p2*q0
         ∧ r3 == p1*q2 + p2*q1
         ∧ r4 == p2*q2

Toom-3 evaluates P and Q at five points (0, 1, -1, 2, ∞), does
five scalar multiplications, then interpolates R from the five
evaluations.  This is the next step in the
Karatsuba/Strassen-style template-search line:

    Karatsuba 2×1 → 3 mults  (proven optimal — bilinear rank 3)
    Toom-3 3×1   → 5 mults  (proven optimal over commutative
                              rings for deg-2 × deg-2)
    Strassen 2×2 → 7 mults  (proven optimal — Hopcroft-Kerr 1971)
    Laderman 3×3 → 23 mults (best known; lower bound ~19;
                              ACTIVE OPEN PROBLEM)

So Toom-3 is, like Karatsuba and Strassen 2×2, a settled case.
The value of verifying it: same template-search machinery applied
to the next-largest setting, plus a real test of whether our IR's
integer division handles the interpolation cleanly.

The interpolation challenge
---------------------------
Toom-3 interpolation has rational coefficients:
    r0 = m0
    r4 = m4
    r2 = (m1 + m2) / 2 - m0 - m4
    r3 = (m3 + 3*m0 - 3*m1 - m2 - 12*m4) / 6
    r1 = (m1 - m2) / 2 - r3

The numerators are ALWAYS divisible (polynomial identity), so
the integer-arithmetic version is exact.  Open question: does
Z3 prove the divisibility?  If not, we may need to either
(a) verify the SCALED algorithm (6*r_i instead of r_i), or
(b) supply axioms tying integer division to multiplication.

Likely outcome
--------------
- Naive (#1) verifies trivially (9 mults, direct from spec).
- Toom-3 (#0) probably needs Z3 to expand polynomial identities
  AND derive divisibility.  Z3 is good at the first, uncertain
  on the second.  Expecting either success or a clear "needs
  axiom for `(divisible_by_6)*k // 6 == k`"-style blocker.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-17.
# Both candidates verify: #0 naive 9-mult (score=5) and #1 Toom-3
# 5-mult (score=10).  Notably, Z3 derives polynomial-identity
# divisibility under integer floor division automatically — the
# `// 2` and `// 6` interpolation steps prove exact via NRA
# expansion of the underlying polynomial.  A wrong-coefficient
# Toom-3 (e.g., `// 3` instead of `// 2`) is correctly rejected.
# Runtime: ~5s.


# Toom-3 with 5 scalar multiplications + integer-division
# interpolation.  Each m_i is one scalar multiplication.
_TOOM3_SSA = [
    # Five evaluation-point multiplications.
    {"m0": "p0 * q0"},                           # P(0)  * Q(0)
    {"m1": "(p0 + p1 + p2) * (q0 + q1 + q2)"},   # P(1)  * Q(1)
    {"m2": "(p0 - p1 + p2) * (q0 - q1 + q2)"},   # P(-1) * Q(-1)
    {"m3": "(p0 + 2*p1 + 4*p2) * (q0 + 2*q1 + 4*q2)"},  # P(2) * Q(2)
    {"m4": "p2 * q2"},                           # P(∞) * Q(∞)
    # Interpolation (rational coefficients, but always exact).
    {"r0": "m0"},
    {"r4": "m4"},
    {"r2": "(m1 + m2) // 2 - m0 - m4"},
    {"r3": "(m3 + 3*m0 - 3*m1 - m2 - 12*m4) // 6"},
    {"r1": "(m1 - m2) // 2 - r3"},
]


# Naive 9-multiplication implementation.
_NAIVE_PARALLEL = {
    "r0": "p0 * q0",
    "r1": "p0 * q1 + p1 * q0",
    "r2": "p0 * q2 + p1 * q1 + p2 * q0",
    "r3": "p1 * q2 + p2 * q1",
    "r4": "p2 * q2",
}


_ALL_ZEROS = {f"r{i}": "0" for i in range(5)}


PROBLEM = Problem(
    description = (
        "Multiply two degree-2 polynomials "
        "(P = p0 + p1·x + p2·x², Q = q0 + q1·x + q2·x²) "
        "yielding their degree-4 product "
        "R = r0 + r1·x + r2·x² + r3·x³ + r4·x⁴."
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

    atoms = {
        "s@B0": [
            _TOOM3_SSA,
            _NAIVE_PARALLEL,
            _ALL_ZEROS,
        ],
    },
    max_solutions = 5,
    expected_solutions = None,  # stretch
    solver_timeout_ms = 600_000,  # 10 min
)


if __name__ == "__main__":
    print(f"toom3_deg2 — XFAIL_REASON: {XFAIL_REASON!r}")
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
