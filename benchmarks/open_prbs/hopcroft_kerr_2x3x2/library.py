"""library.py — verified mat-mul algorithm library for L1.2
speculation/discovery framework.

Each entry is a tensor decomposition with concrete (L_a, L_b, γ)
matrices and a Lean axiom asserting its correctness.  The
framework uses these as FIXED building blocks when searching
for compositions at larger problems.

Library entries are Z3-kernel-verifiable (polynomial-identity
check) and Lean-emittable (synth framework's Tier-1 path).
"""

# Strassen 1969: 2×2 × 2×2 in 7 multiplications.
#
# Inputs (4 + 4 = 8 entries):
#   A = [a00 a01]    B = [b00 b01]
#       [a10 a11]        [b10 b11]
# Outputs (4 entries):
#   D = A·B = [d00 d01]
#             [d10 d11]
#   d_ij = a_i0·b_0j + a_i1·b_1j.
#
# 7 bilinear products + γ combining:
#   m0 = (a00 + a11)(b00 + b11)
#   m1 = (a10 + a11) b00
#   m2 = a00 (b01 - b11)
#   m3 = a11 (b10 - b00)
#   m4 = (a00 + a01) b11
#   m5 = (a10 - a00)(b00 + b01)
#   m6 = (a01 - a11)(b10 + b11)
#
#   d00 = m0 + m3 - m4 + m6
#   d01 = m2 + m4
#   d10 = m1 + m3
#   d11 = m0 - m1 + m2 + m5
STRASSEN_2x2 = {
    "name": "strassen_2x2",
    "n_a": 4,  # A entries (a00, a01, a10, a11)
    "n_b": 4,  # B entries
    "m_out": 4,  # D entries (d00, d01, d10, d11)
    "K": 7,
    # L_a[k][i] ∈ {-1, 0, +1}: coefficient of A[i] in m_k's left factor.
    # Indexing: A = (a00, a01, a10, a11) → index 0..3.
    "L_a": [
        [ 1,  0,  0,  1],   # m0: a00 + a11
        [ 0,  0,  1,  1],   # m1: a10 + a11
        [ 1,  0,  0,  0],   # m2: a00
        [ 0,  0,  0,  1],   # m3: a11
        [ 1,  1,  0,  0],   # m4: a00 + a01
        [-1,  0,  1,  0],   # m5: a10 - a00
        [ 0,  1,  0, -1],   # m6: a01 - a11
    ],
    # L_b[k][i]: coefficient of B[i] in m_k's right factor.
    # B = (b00, b01, b10, b11) → index 0..3.
    "L_b": [
        [ 1,  0,  0,  1],   # m0: b00 + b11
        [ 1,  0,  0,  0],   # m1: b00
        [ 0,  1,  0, -1],   # m2: b01 - b11
        [-1,  0,  1,  0],   # m3: b10 - b00
        [ 0,  0,  0,  1],   # m4: b11
        [ 1,  1,  0,  0],   # m5: b00 + b01
        [ 0,  0,  1,  1],   # m6: b10 + b11
    ],
    # γ[j][k] ∈ {-1, 0, +1}: coefficient of m_k in d_j.
    # j = 0 → d00, 1 → d01, 2 → d10, 3 → d11.
    "gamma": [
        [ 1,  0,  0,  1, -1,  0,  1],   # d00 = m0 + m3 - m4 + m6
        [ 0,  0,  1,  0,  1,  0,  0],   # d01 = m2 + m4
        [ 0,  1,  0,  1,  0,  0,  0],   # d10 = m1 + m3
        [ 1, -1,  1,  0,  0,  1,  0],   # d11 = m0 - m1 + m2 + m5
    ],
    # Lean axiom (when emitted): strassen_2x2_correct.
    "lean_axiom": "strassen_2x2_correct",
}


# 2×1 × 1×2 outer product: K=4 trivially.
#   u = (u0, u1)^T (column), v = (v0, v1) (row).
#   u·v = [u0 v0  u0 v1]
#         [u1 v0  u1 v1]
#
# 4 mults: m0 = u0 v0; m1 = u0 v1; m2 = u1 v0; m3 = u1 v1.
# γ is identity per output.
OUTER_PRODUCT_2x1_1x2 = {
    "name": "outer_2x1_1x2",
    "n_a": 2,
    "n_b": 2,
    "m_out": 4,  # outputs flat: (out00, out01, out10, out11)
    "K": 4,
    "L_a": [
        [1, 0],  # m0: u0
        [1, 0],  # m1: u0
        [0, 1],  # m2: u1
        [0, 1],  # m3: u1
    ],
    "L_b": [
        [1, 0],  # m0: v0
        [0, 1],  # m1: v1
        [1, 0],  # m2: v0
        [0, 1],  # m3: v1
    ],
    "gamma": [
        [1, 0, 0, 0],  # out00 = m0
        [0, 1, 0, 0],  # out01 = m1
        [0, 0, 1, 0],  # out10 = m2
        [0, 0, 0, 1],  # out11 = m3
    ],
    "lean_axiom": "outer_product_2x1_1x2_correct",
}


# Naive 2×2 × 2×2: K=8 (no sharing).
# d_ij = a_i0·b_0j + a_i1·b_1j.
# 4 outputs × 2 mults each = 8.
NAIVE_2x2 = {
    "name": "naive_2x2",
    "n_a": 4, "n_b": 4, "m_out": 4, "K": 8,
    "L_a": [
        [1, 0, 0, 0],  # m0: a00 (for d00)
        [0, 1, 0, 0],  # m1: a01 (for d00)
        [1, 0, 0, 0],  # m2: a00 (for d01)
        [0, 1, 0, 0],  # m3: a01 (for d01)
        [0, 0, 1, 0],  # m4: a10 (for d10)
        [0, 0, 0, 1],  # m5: a11 (for d10)
        [0, 0, 1, 0],  # m6: a10 (for d11)
        [0, 0, 0, 1],  # m7: a11 (for d11)
    ],
    "L_b": [
        [1, 0, 0, 0], [0, 0, 1, 0],
        [0, 1, 0, 0], [0, 0, 0, 1],
        [1, 0, 0, 0], [0, 0, 1, 0],
        [0, 1, 0, 0], [0, 0, 0, 1],
    ],
    "gamma": [
        [1, 1, 0, 0, 0, 0, 0, 0],  # d00
        [0, 0, 1, 1, 0, 0, 0, 0],  # d01
        [0, 0, 0, 0, 1, 1, 0, 0],  # d10
        [0, 0, 0, 0, 0, 0, 1, 1],  # d11
    ],
    "lean_axiom": "naive_2x2_correct",
}


LIBRARY = {
    "strassen_2x2": STRASSEN_2x2,
    "outer_2x1_1x2": OUTER_PRODUCT_2x1_1x2,
    "naive_2x2": NAIVE_2x2,
}
