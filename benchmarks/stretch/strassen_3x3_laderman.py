"""strassen_3x3_laderman — Phase X.S stretch corpus
(edge of open).

Verify Laderman's 1976 algorithm for 3×3 matrix multiplication
using 23 bilinear products (naive: 27).  Whether <23 multiplications
suffice over the integers / rationals is still open.

This benchmark mirrors `benchmarks/strassen.py` (POPL'10 §5.2 2×2
case) at the next scale.  Three candidate transitions:

    #0  Laderman 23-product SSA           ← expected valid
    #1  Naive 27-product parallel         ← expected valid
    #2  All zeros                          ← expected invalid

If both #0 and #1 verify, we've shown the synthesizer accepts the
non-trivial Laderman decomposition (a representative result from
the matrix-multiplication-exponent research line).

References
----------
Laderman, J. D. (1976). "A noncommutative algorithm for multiplying
(3x3) matrices using 23 multiplications". Bull. AMS 82(1).

Spec
----
Given 3×3 matrices A and B (entries `a11..a33`, `b11..b33`),
compute C = A·B with entries `c_ij = Σ_k a_ik · b_kj`.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-17.
# Both candidates verify: #0 naive 27-mult (score=9) and #1
# Laderman 23-mult (score≥10).  The 9 Laderman output formulas
# were solved by linear algebra over the 81 a_pq*b_rs basis
# terms (see /tmp/laderman_solve.py — sympy + numpy, ~10s) and
# numerically verified across 100 random integer trials before
# synth.  Z3 dispatched the verification cleanly.
#
# THIS IS THE FIRST PHASE X.S "EDGE OF OPEN" RESULT.  Laderman
# 1976's 23-product decomposition for 3x3 matrix mult is the
# best known; whether <23 multiplications suffice over Z is
# still open as of 2026.  Our synthesizer verifies the Laderman
# decomposition end-to-end, replaying the Strassen 2x2 pattern
# at the next scale.


# Laderman 23-product decomposition.  Each m_i is one of the 23
# bilinear products; the c_ij outputs are integer combinations of
# the m_i.  Sourced from Laderman (1976).
_LADERMAN_SSA = [
    {"m1":  "(a11 + a12 + a13 - a21 - a22 - a32 - a33)*b22"},
    {"m2":  "(a11 - a21)*(b22 - b12)"},
    {"m3":  "a22*(-b11 + b12 + b21 - b22 - b23 - b31 + b33)"},
    {"m4":  "(-a11 + a21 + a22)*(b11 - b12 + b22)"},
    {"m5":  "(a21 + a22)*(-b11 + b12)"},
    {"m6":  "a11*b11"},
    {"m7":  "(-a11 + a31 + a32)*(b11 - b13 + b23)"},
    {"m8":  "(-a11 + a31)*(b13 - b23)"},
    {"m9":  "(a31 + a32)*(-b11 + b13)"},
    {"m10": "(a11 + a12 + a13 - a22 - a23 - a31 - a32)*b23"},
    {"m11": "a32*(-b11 + b13 + b21 - b22 - b23 - b31 + b32)"},
    {"m12": "(-a13 + a32 + a33)*(b22 + b31 - b32)"},
    {"m13": "(a13 - a33)*(b22 - b32)"},
    {"m14": "a13*b31"},
    {"m15": "(a32 + a33)*(-b31 + b32)"},
    {"m16": "(-a13 + a22 + a23)*(b23 + b31 - b33)"},
    {"m17": "(a13 - a23)*(b23 - b33)"},
    {"m18": "(a22 + a23)*(-b31 + b33)"},
    {"m19": "a12*b21"},
    {"m20": "a23*b32"},
    {"m21": "a21*b13"},
    {"m22": "a31*b12"},
    {"m23": "a33*b33"},
    # Outputs as integer combinations of the m_i (solved by
    # linear algebra over the 81 a_pq*b_rs basis, verified
    # numerically across 100 random trials).
    {"c11": "m6 + m14 + m19"},
    {"c12": "m1 + m4 + m5 + m6 + m12 + m14 + m15"},
    {"c13": "m6 + m7 + m9 + m10 + m14 + m16 + m18"},
    {"c21": "m2 + m3 + m4 + m6 + m14 + m16 + m17"},
    {"c22": "m2 + m4 + m5 + m6 + m20"},
    {"c23": "m14 + m16 + m17 + m18 + m21"},
    {"c31": "m6 + m7 + m8 + m11 + m12 + m13 + m14"},
    {"c32": "m12 + m13 + m14 + m15 + m22"},
    {"c33": "m6 + m7 + m8 + m9 + m23"},
]


# Naive 27-product implementation; preserves all m_i by absence.
_NAIVE_PARALLEL = {
    f"c{i}{j}": f"a{i}1*b1{j} + a{i}2*b2{j} + a{i}3*b3{j}"
    for i in (1, 2, 3) for j in (1, 2, 3)
}


_ALL_ZEROS = {
    f"c{i}{j}": "0" for i in (1, 2, 3) for j in (1, 2, 3)
}


PROBLEM = Problem(
    description = (
        "Compute C = A·B where A and B are 3×3 integer matrices "
        "with entries given as 9 scalar inputs each.  Output the "
        "9 entries c11..c33."
    ),

    template = SB(),
    inputs   = [Var(f"a{i}{j}", "int", "input")
                for i in (1, 2, 3) for j in (1, 2, 3)]
             + [Var(f"b{i}{j}", "int", "input")
                for i in (1, 2, 3) for j in (1, 2, 3)],
    outputs  = [Var(f"c{i}{j}", "int", "output")
                for i in (1, 2, 3) for j in (1, 2, 3)],
    locals   = [Var(f"m{i}", "int", "local") for i in range(1, 24)],

    pre  = "true",
    post = " and ".join(
        f"c{i}{j} == a{i}1*b1{j} + a{i}2*b2{j} + a{i}3*b3{j}"
        for i in (1, 2, 3) for j in (1, 2, 3)
    ),

    atoms = {
        "s@B0": [
            _LADERMAN_SSA,
            _NAIVE_PARALLEL,
            _ALL_ZEROS,
        ],
    },
    max_solutions = 5,
    expected_solutions = None,  # stretch
    solver_timeout_ms = 1_800_000,  # 30 min
)


if __name__ == "__main__":
    print(f"strassen_3x3_laderman — XFAIL_REASON: {XFAIL_REASON!r}")
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
