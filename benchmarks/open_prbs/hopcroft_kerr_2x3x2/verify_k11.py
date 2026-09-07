"""verify_k11.py — verify the Hopcroft-Kerr 11-mult algorithm for
2×3 × 3×2 matrix multiplication over ℤ via the synth framework.

This is a VERIFICATION benchmark, not a discovery search.  The
recipe is the published Hopcroft-Kerr construction:

  Block decomposition: A = [A_left | A_right] with A_left (2×2),
                       A_right (2×1).  B = [B_top; B_bot].
  Sub-algorithms:
    A_left · B_top via Strassen 1969 (7 mults).
    A_right · B_bot via naive outer product (4 mults).

The synth framework verifies the SSA recipe against the
matrix-multiplication identity (Z3 polynomial check; Lean
backend can emit a kernel-checked theorem).

Indexing:
  A entries: a00, a01, a02, a10, a11, a12   (2×3 matrix)
  B entries: b00, b01, b10, b11, b20, b21   (3×2 matrix)
  C entries: c00, c01, c10, c11              (2×2 result)

Spec:
  c[i][j] = Σ_k a[i][k] · b[k][j]
  Concretely:
    c00 = a00·b00 + a01·b10 + a02·b20
    c01 = a00·b01 + a01·b11 + a02·b21
    c10 = a10·b00 + a11·b10 + a12·b20
    c11 = a10·b01 + a11·b11 + a12·b21

If both candidates verify (the K=11 Strassen+outer and the
K=12 naive baseline), the synth framework has produced a
verified algorithm artifact at the Hopcroft-Kerr bound — a
useful starting point for the K=10 discovery search.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None


# K=11: Strassen (7) on 2×2×2 left block + outer product (4) on 2×1·1×2 right.
_HOPCROFT_KERR_K11 = [
    # Strassen 7 mults applied to A_left = [a00 a01; a10 a11], B_top = [b00 b01; b10 b11]
    {"m0": "(a00 + a11) * (b00 + b11)"},
    {"m1": "(a10 + a11) * b00"},
    {"m2": "a00 * (b01 - b11)"},
    {"m3": "a11 * (b10 - b00)"},
    {"m4": "(a00 + a01) * b11"},
    {"m5": "(a10 - a00) * (b00 + b01)"},
    {"m6": "(a01 - a11) * (b10 + b11)"},
    # Outer product 4 mults on A_right = [a02; a12], B_bot = [b20 b21]
    {"m7":  "a02 * b20"},
    {"m8":  "a02 * b21"},
    {"m9":  "a12 * b20"},
    {"m10": "a12 * b21"},
    # Combine.  C = A_left·B_top + A_right·B_bot.
    # Strassen 2×2 outputs (for A_left·B_top):
    #   c'00 = m0 + m3 - m4 + m6
    #   c'01 = m2 + m4
    #   c'10 = m1 + m3
    #   c'11 = m0 - m1 + m2 + m5
    # Add outer-product contributions:
    {"c00": "m0 + m3 - m4 + m6 + m7"},
    {"c01": "m2 + m4 + m8"},
    {"c10": "m1 + m3 + m9"},
    {"c11": "m0 - m1 + m2 + m5 + m10"},
]


# K=12 naive: 3 multiplications per output, no sharing.
_NAIVE_K12 = {
    "c00": "a00*b00 + a01*b10 + a02*b20",
    "c01": "a00*b01 + a01*b11 + a02*b21",
    "c10": "a10*b00 + a11*b10 + a12*b20",
    "c11": "a10*b01 + a11*b11 + a12*b21",
}


_A_VARS = ["a00", "a01", "a02", "a10", "a11", "a12"]
_B_VARS = ["b00", "b01", "b10", "b11", "b20", "b21"]
_C_VARS = ["c00", "c01", "c10", "c11"]


PROBLEM = Problem(
    description = (
        "Verify the Hopcroft-Kerr 1971 11-multiplication algorithm "
        "for 2×3 × 3×2 matrix multiplication over ℤ, via block "
        "decomposition: Strassen (7 mults) on the 2×2 left block "
        "plus naive outer product (4 mults) on the 2×1 right block."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input") for n in _A_VARS + _B_VARS],
    outputs  = [Var(n, "int", "output") for n in _C_VARS],
    locals   = [Var(f"m{i}", "int", "local") for i in range(11)],

    pre  = "true",
    post = (
        f"{_C_VARS[0]} == a00*b00 + a01*b10 + a02*b20 and "
        f"{_C_VARS[1]} == a00*b01 + a01*b11 + a02*b21 and "
        f"{_C_VARS[2]} == a10*b00 + a11*b10 + a12*b20 and "
        f"{_C_VARS[3]} == a10*b01 + a11*b11 + a12*b21"
    ),

    atoms = {
        "s@B0": [
            _HOPCROFT_KERR_K11,
            _NAIVE_K12,
        ],
    },
    max_solutions = 5,
    expected_solutions = None,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    print(f"verify_k11 — XFAIL_REASON: {XFAIL_REASON!r}")
    print(f"Goal: verify 11-mult Hopcroft-Kerr + 12-mult naive for")
    print(f"      2×3 × 3×2 matrix multiplication over ℤ.")
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
