"""encoding_joint.py — joint bilinear + SLP encoding for K=7 2×2 matmul.

Searches simultaneously for:
  - A valid bilinear-form decomposition (α, β, γ) with K=7 ±1 coefs.
  - An SLP with budget L_A + L_B + L_G binary adds whose outputs
    equal those bilinear coefs.

The bilinear tensor identity is encoded in FLAT BOOLEAN (no NIA);
the SLP unfolding is LINEAR in Int (QF_LIA).  The two are tied
by Int equality between the SLP output and the (pos − neg) Int
representation of the bilinear coefs.

For total SLP budget T = L_A + L_B + L_G:
  - T = 18: Strassen's classical count.
  - T = 15: Heun-optimal ±1-coef SLP count (Probert lower bound).
  - T = 12: Karstadt-Schwartz target.
  - T < 12: would beat Karstadt-Schwartz.
"""
from z3 import (And, Bool, BoolVal, If, Int, Not, Or, Solver,
                Sum, Xor, sat, unsat, set_param)

from encoding import (
    make_vars, add_disjoint, add_tensor_constraints, add_nontrivial,
    add_sym_break, nonzero_count_expr, extract_model, verify_witness,
    count_nonzeros, print_witness,
    N_A, N_B, M,
)

K = 7


def add_slp_for_side(solver, L, base_count, K_forms, name_prefix,
                     unfolded_target_coefs):
    """Encode an SLP that produces K_forms linear forms over base_count
    base inputs, each with ±1 coefs given in `unfolded_target_coefs`.

    unfolded_target_coefs: list of K_forms vectors, each is a list of
    base_count Int expressions (the bilinear coefs, expected ∈ {-1,0,+1}).

    Returns nothing; constraints are added to `solver`.
    """
    intermediates = []  # list of coef-vectors

    def base_vec(i):
        return [1 if k == i else 0 for k in range(base_count)]

    for l in range(L):
        n_src = base_count + l
        src1 = Int(f"{name_prefix}_src1_{l}")
        src2 = Int(f"{name_prefix}_src2_{l}")
        sgn1 = Bool(f"{name_prefix}_sgn1_{l}")
        sgn2 = Bool(f"{name_prefix}_sgn2_{l}")
        solver.add(src1 >= 0, src1 < n_src)
        solver.add(src2 >= 0, src2 < n_src)
        solver.add(src1 < src2)

        available = [base_vec(i) for i in range(base_count)] + intermediates[:]
        coef_vec = []
        for entry_idx in range(base_count):
            v1_terms = []
            for choice in range(n_src):
                src_coef = available[choice][entry_idx]
                v1_terms.append(
                    If(src1 == choice,
                       If(sgn1, -src_coef, src_coef),
                       0))
            v2_terms = []
            for choice in range(n_src):
                src_coef = available[choice][entry_idx]
                v2_terms.append(
                    If(src2 == choice,
                       If(sgn2, -src_coef, src_coef),
                       0))
            coef_vec.append(Sum(v1_terms) + Sum(v2_terms))
        intermediates.append(coef_vec)

    # For each form, pick a source from {base ∪ intermediates} with sign.
    all_sources = [base_vec(i) for i in range(base_count)] + intermediates[:]
    total_sources = base_count + L
    for n, target in enumerate(unfolded_target_coefs):
        pick = Int(f"{name_prefix}_pick_{n}")
        pick_sgn = Bool(f"{name_prefix}_sgn_{n}")
        solver.add(pick >= 0, pick < total_sources)
        for entry_idx in range(base_count):
            terms = []
            for choice in range(total_sources):
                src_coef = all_sources[choice][entry_idx]
                terms.append(
                    If(pick == choice,
                       If(pick_sgn, -src_coef, src_coef),
                       0))
            solver.add(Sum(terms) == target[entry_idx])


def build_joint_search(L_A, L_B, L_G, sym_break=True):
    """Joint Z3 encoding: K=7 ±1 bilinear + SLP costs L_A, L_B, L_G."""
    solver = Solver()
    a_p, a_n, b_p, b_n, g_p, g_n = make_vars(K)
    add_disjoint(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)
    add_tensor_constraints(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)
    add_nontrivial(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)
    if sym_break:
        add_sym_break(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)

    # Build Int "target" vectors for the SLP to produce.
    # alpha_target[k][i] = (a_p - a_n) as Int.
    alpha_target = [
        [If(a_p[k][i], 1, 0) - If(a_n[k][i], 1, 0) for i in range(N_A)]
        for k in range(K)
    ]
    beta_target = [
        [If(b_p[k][i], 1, 0) - If(b_n[k][i], 1, 0) for i in range(N_B)]
        for k in range(K)
    ]
    # gamma_target[j][k] = γ[j][k], stored row-major.
    # SLP for γ produces M forms over K inputs (m_0..m_6).
    gamma_target = [
        [If(g_p[j][k], 1, 0) - If(g_n[j][k], 1, 0) for k in range(K)]
        for j in range(M)
    ]

    add_slp_for_side(solver, L_A, N_A, K, "sA", alpha_target)
    add_slp_for_side(solver, L_B, N_B, K, "sB", beta_target)
    add_slp_for_side(solver, L_G, K, M, "sG", gamma_target)

    return solver, a_p, a_n, b_p, b_n, g_p, g_n


def search_joint(L_A, L_B, L_G, timeout_s=600, verbose=True):
    """Run joint search at given (L_A, L_B, L_G).  Returns (verdict, elapsed, witness)."""
    import time
    set_param("parallel.enable", True)
    solver, a_p, a_n, b_p, b_n, g_p, g_n = build_joint_search(L_A, L_B, L_G)
    solver.set("timeout", timeout_s * 1000)
    if verbose:
        print(f"  Joint search L_A={L_A}, L_B={L_B}, L_G={L_G} (total {L_A+L_B+L_G})")
    t0 = time.monotonic()
    r = solver.check()
    elapsed = time.monotonic() - t0
    if r == sat:
        m = solver.model()
        alpha, beta, gamma = extract_model(m, a_p, a_n, b_p, b_n, g_p, g_n, K)
        return "sat", elapsed, (alpha, beta, gamma)
    elif r == unsat:
        return "unsat", elapsed, None
    else:
        return "timeout", elapsed, None


def sweep_total(total, timeout_s=600, ordered=False):
    """Sweep all (L_A, L_B, L_G) splits with sum = total.

    By A↔B symmetry, only enumerate L_A ≤ L_B.
    """
    import sys
    print(f"Joint sweep at total = {total} SLP binary adds.")
    splits = []
    for L_A in range(0, total + 1):
        for L_B in range(L_A, total - L_A + 1):
            L_G = total - L_A - L_B
            splits.append((L_A, L_B, L_G))
    if ordered:
        # heuristic: prefer balanced splits first
        splits.sort(key=lambda x: max(x) - min(x))

    sat_found = []
    for L_A, L_B, L_G in splits:
        verdict, elapsed, witness = search_joint(L_A, L_B, L_G, timeout_s,
                                                  verbose=True)
        print(f"    Z3: {verdict}  ({elapsed:.2f}s)")
        sys.stdout.flush()
        if verdict == "sat":
            sat_found.append((L_A, L_B, L_G, elapsed, witness))
            print(f"    *** SAT: total = {total} ({L_A}+{L_B}+{L_G}) ***")
            alpha, beta, gamma = witness
            ok, fail = verify_witness(alpha, beta, gamma, K)
            if not ok:
                print(f"    VERIFY-FAIL: {fail}")
            else:
                print_witness(alpha, beta, gamma, K,
                              label=f"joint SLP={total} witness")

    return sat_found
