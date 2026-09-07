"""encoding_slp.py — Straight-Line Program (SLP) encoding for K=7 2×2 matmul
addition minimization.

The "additions count" minimized by Karstadt-Schwartz 2017 is NOT the
literal nonzero count of the bilinear decomposition (≥ 33 by Heun 1994),
but rather the operation count of a straight-line program (SLP) that
computes the 7 multiplications.  Shared intermediate sub-expressions
are computed once; this is what allows the K-S count to drop below
Heun's 15-add lower bound.

Encoding:
  - A-side SLP: L_A intermediate forms s_1, ..., s_{L_A}.
    Each s_l = sign_a · src_a + sign_b · src_b where each src is
    one of the base inputs {a, b, c, d} or any earlier s_{l'} (l' < l).
    Each defines ONE binary addition/subtraction.
  - B-side SLP: L_B intermediate forms t_1, ..., t_{L_B} similarly
    over {e, f, g, h} ∪ {earlier t}.
  - γ-side SLP: L_G intermediate forms u_1, ..., u_{L_G} over the
    7 mults {m_0, ..., m_6} ∪ {earlier u}.
  - Each m_k.left_factor = one of {a, b, c, d, s_1, ..., s_{L_A}}
    (with optional sign).
  - Each m_k.right_factor = one of {e, f, g, h, t_1, ..., t_{L_B}}
    (with optional sign).
  - Each output C_j = one of {m_0, ..., m_6, u_1, ..., u_{L_G}} OR
    a 2-term combination m + s_u (extension).

For the canonical form: every m_k's left/right factor is a SINGLE
form (input or intermediate); every output is a SINGLE form (mult
or intermediate).  Then the total ADDITIONS count is exactly
L_A + L_B + L_G (each intermediate is one binary add).

This is the "narrowest SLP model" — it forces sharing maximally and
gives an UPPER bound on the K-S count.  If we find L_A + L_B + L_G = 12
SAT with K=7 + valid bilinear decomposition, we've matched K-S.

Variables (per SLP definition s_l, t_l, u_l):
  src1, src2 ∈ {0, 1, ..., l + base_count - 1}
  sign1, sign2 ∈ {+1, -1}

Each m_k:
  left_src  ∈ {0, ..., N_A + L_A - 1}
  left_sign ∈ {+1, -1}
  right_src ∈ {0, ..., N_B + L_B - 1}
  right_sign ∈ {+1, -1}

Each output C_j:
  out_src  ∈ {0, ..., K + L_G - 1}
  out_sign ∈ {+1, -1}

We unfold each form symbolically to a vector of ±1 coefficients
over the base inputs, then assert the tensor identity.  Z3 picks
the SLP assignment + signs that satisfies the identity.

For K=7, L_A=L_B=L_G=4 → 12 additions total — the K-S target.
For K=7, L_A+L_B+L_G < 12 → sub-K-S target.
"""
from z3 import (And, Bool, BoolVal, If, Int, Not, Or, Solver, Sum,
                Xor, sat, unsat)

N_A = 4
N_B = 4
M   = 4


def target_tensor():
    T = [[[0] * N_B for _ in range(N_A)] for _ in range(M)]
    for i in range(2):
        for j in range(2):
            c_idx = i * 2 + j
            for k in range(2):
                a_idx = i * 2 + k
                b_idx = k * 2 + j
                T[c_idx][a_idx][b_idx] = 1
    return T


def encode_slp(K, L_A, L_B, L_G, sym_break=True):
    """Build the SLP-encoded search for K mults with L_A + L_B + L_G additions.

    Returns (solver, vars_dict).  Variables are integer-valued src indices
    + boolean sign flags, plus expanded coefficient vectors for each form.
    """
    solver = Solver()

    # ---- A-side SLP: s_l (l=1..L_A), each is a 2-term combo over
    # {a, b, c, d, s_1, ..., s_{l-1}}.
    # We unfold each s_l to a coefficient vector over (a, b, c, d).
    # Base inputs a, b, c, d have coefficient vectors as standard basis e_0..e_3.

    def base_a_vec(i):
        return [1 if k == i else 0 for k in range(N_A)]

    # s_l's coefficient vector over (a, b, c, d): list of L_A vectors.
    s_vecs = []  # list of (Int) coefficient vectors after SLP eval
    s_choices = []  # bookkeeping
    for l in range(L_A):
        # Available sources: N_A base + l previous intermediates.
        n_src = N_A + l
        src1 = Int(f"sA_src1_{l}")
        src2 = Int(f"sA_src2_{l}")
        sgn1 = Bool(f"sA_sgn1_{l}")  # True → -1, False → +1
        sgn2 = Bool(f"sA_sgn2_{l}")
        solver.add(src1 >= 0, src1 < n_src)
        solver.add(src2 >= 0, src2 < n_src)
        solver.add(src1 != src2)  # binary add must use 2 distinct sources
        # Order: src1 < src2 to break add-commutativity sym.
        solver.add(src1 < src2)

        # Compute s_l's coefficient vector by selecting src1, src2 from
        # available list (base + earlier s) and combining.
        available = [base_a_vec(i) for i in range(N_A)] + s_vecs[:]
        # Build the coefficient vector entry-by-entry.
        coef_vec = []
        for entry_idx in range(N_A):
            # Sum of (sign·available[src1][entry_idx]) for the chosen src.
            v1_terms = []
            for choice in range(n_src):
                v1_terms.append(
                    If(src1 == choice,
                       If(sgn1, -available[choice][entry_idx], available[choice][entry_idx]),
                       0))
            v2_terms = []
            for choice in range(n_src):
                v2_terms.append(
                    If(src2 == choice,
                       If(sgn2, -available[choice][entry_idx], available[choice][entry_idx]),
                       0))
            coef_vec.append(Sum(v1_terms) + Sum(v2_terms))
        s_vecs.append(coef_vec)
        s_choices.append((src1, src2, sgn1, sgn2))

    def base_b_vec(i):
        return [1 if k == i else 0 for k in range(N_B)]

    t_vecs = []
    t_choices = []
    for l in range(L_B):
        n_src = N_B + l
        src1 = Int(f"sB_src1_{l}")
        src2 = Int(f"sB_src2_{l}")
        sgn1 = Bool(f"sB_sgn1_{l}")
        sgn2 = Bool(f"sB_sgn2_{l}")
        solver.add(src1 >= 0, src1 < n_src)
        solver.add(src2 >= 0, src2 < n_src)
        solver.add(src1 != src2)
        solver.add(src1 < src2)
        available = [base_b_vec(i) for i in range(N_B)] + t_vecs[:]
        coef_vec = []
        for entry_idx in range(N_B):
            v1_terms = []
            for choice in range(n_src):
                v1_terms.append(
                    If(src1 == choice,
                       If(sgn1, -available[choice][entry_idx], available[choice][entry_idx]),
                       0))
            v2_terms = []
            for choice in range(n_src):
                v2_terms.append(
                    If(src2 == choice,
                       If(sgn2, -available[choice][entry_idx], available[choice][entry_idx]),
                       0))
            coef_vec.append(Sum(v1_terms) + Sum(v2_terms))
        t_vecs.append(coef_vec)
        t_choices.append((src1, src2, sgn1, sgn2))

    # ---- Each m_k's left factor: pick from {a, b, c, d, s_1, ..., s_{L_A}}.
    # Right factor: pick from {e, f, g, h, t_1, ..., t_{L_B}}.
    # Sign for each.
    a_available = [base_a_vec(i) for i in range(N_A)] + s_vecs[:]
    b_available = [base_b_vec(i) for i in range(N_B)] + t_vecs[:]

    m_left_vecs = []   # m_k's coef vector over (a, b, c, d)
    m_right_vecs = []  # m_k's coef vector over (e, f, g, h)
    m_choices = []
    for k in range(K):
        l_src = Int(f"m_lsrc_{k}")
        l_sgn = Bool(f"m_lsgn_{k}")
        r_src = Int(f"m_rsrc_{k}")
        r_sgn = Bool(f"m_rsgn_{k}")
        solver.add(l_src >= 0, l_src < len(a_available))
        solver.add(r_src >= 0, r_src < len(b_available))

        left_vec = []
        for entry_idx in range(N_A):
            terms = []
            for choice in range(len(a_available)):
                terms.append(
                    If(l_src == choice,
                       If(l_sgn, -a_available[choice][entry_idx], a_available[choice][entry_idx]),
                       0))
            left_vec.append(Sum(terms))
        right_vec = []
        for entry_idx in range(N_B):
            terms = []
            for choice in range(len(b_available)):
                terms.append(
                    If(r_src == choice,
                       If(r_sgn, -b_available[choice][entry_idx], b_available[choice][entry_idx]),
                       0))
            right_vec.append(Sum(terms))
        m_left_vecs.append(left_vec)
        m_right_vecs.append(right_vec)
        m_choices.append((l_src, l_sgn, r_src, r_sgn))

    # ---- γ SLP: u_l ∈ {m_0, ..., m_6, u_1, ..., u_{l-1}}.
    # γ vector over m_0..m_6 (length K).
    def base_m_vec(k):
        return [1 if k_ == k else 0 for k_ in range(K)]

    u_vecs = []
    u_choices = []
    for l in range(L_G):
        n_src = K + l
        src1 = Int(f"u_src1_{l}")
        src2 = Int(f"u_src2_{l}")
        sgn1 = Bool(f"u_sgn1_{l}")
        sgn2 = Bool(f"u_sgn2_{l}")
        solver.add(src1 >= 0, src1 < n_src)
        solver.add(src2 >= 0, src2 < n_src)
        solver.add(src1 != src2)
        solver.add(src1 < src2)
        available = [base_m_vec(k_) for k_ in range(K)] + u_vecs[:]
        coef_vec = []
        for entry_idx in range(K):
            v1_terms = []
            for choice in range(n_src):
                v1_terms.append(
                    If(src1 == choice,
                       If(sgn1, -available[choice][entry_idx], available[choice][entry_idx]),
                       0))
            v2_terms = []
            for choice in range(n_src):
                v2_terms.append(
                    If(src2 == choice,
                       If(sgn2, -available[choice][entry_idx], available[choice][entry_idx]),
                       0))
            coef_vec.append(Sum(v1_terms) + Sum(v2_terms))
        u_vecs.append(coef_vec)
        u_choices.append((src1, src2, sgn1, sgn2))

    # ---- Outputs C_j: pick from {m_0, ..., m_6, u_1, ..., u_{L_G}}.
    out_available = [base_m_vec(k) for k in range(K)] + u_vecs[:]
    gamma_vecs = []  # γ[j] as coef over m_0..m_6
    out_choices = []
    for j in range(M):
        o_src = Int(f"o_src_{j}")
        o_sgn = Bool(f"o_sgn_{j}")
        solver.add(o_src >= 0, o_src < len(out_available))
        gvec = []
        for k in range(K):
            terms = []
            for choice in range(len(out_available)):
                terms.append(
                    If(o_src == choice,
                       If(o_sgn, -out_available[choice][k], out_available[choice][k]),
                       0))
            gvec.append(Sum(terms))
        gamma_vecs.append(gvec)
        out_choices.append((o_src, o_sgn))

    # ---- Tensor identity: T[j][ia][ib] == Σ_k γ[j][k] · α[k][ia] · β[k][ib].
    # Where α[k] = m_left_vecs[k], β[k] = m_right_vecs[k].
    T = target_tensor()
    for j in range(M):
        for ia in range(N_A):
            for ib in range(N_B):
                acc = Sum([gamma_vecs[j][k] * m_left_vecs[k][ia] * m_right_vecs[k][ib]
                           for k in range(K)])
                solver.add(acc == T[j][ia][ib])

    vars_dict = {
        "s_choices": s_choices,
        "t_choices": t_choices,
        "u_choices": u_choices,
        "m_choices": m_choices,
        "out_choices": out_choices,
        "s_vecs": s_vecs,
        "t_vecs": t_vecs,
        "u_vecs": u_vecs,
        "m_left_vecs": m_left_vecs,
        "m_right_vecs": m_right_vecs,
        "gamma_vecs": gamma_vecs,
    }
    return solver, vars_dict
