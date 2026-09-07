"""speculate_k10.py — Lean-axiom speculation search for K=10
algorithm for 2×3 × 3×2 matrix multiplication over ℤ.

Architecture (per user 2026-05-20):
  - Library entry STRASSEN_2x2 (K=7) provides 7 specific bilinear
    products over the A_left (2×2) × B_top (2×2) sub-block.  Its
    correctness is a Lean-verifiable theorem (axiom in the
    search; discharged separately by Z3 polynomial check or
    Lean proof).
  - K_extra ADDITIONAL parametric rank-1 mults span the full
    (A, B) input space.  Their (L_a, L_b) coefficients in
    {-1, 0, +1} are search variables.
  - γ combines all (7 + K_extra) bilinear products to form the
    4 outputs of 2×3 × 3×2.  γ is a parametric matrix in
    {-1, 0, +1}.

For K_extra=4: total K=11, the Hopcroft-Kerr baseline.
For K_extra=3: total K=10, BEATS Hopcroft-Kerr if SAT.

If SAT at K=10, the result is CONDITIONAL on Strassen being
correct (which is a verified Lean theorem).  Discharge: cite
the strassen_2x2_correct axiom from the library.

Encoding: Boolean pos/neg flags per ±1 coefficient (same as the
proven approach from L2.1).  Strassen's 7 bilinear forms are
EXPANDED at encoding time — Z3 sees the specific bilinear
contributions over the full (a, b) input space (with 0 on
A_right/B_bot dimensions).

Search space size (for K_extra=3):
  - 3 extra mults × 6 A bits × 2 (pos/neg) = 36 booleans for L_a.
  - 3 × 6 × 2 = 36 booleans for L_b.
  - 4 outputs × 10 mults (7 Strassen + 3 extra) × 2 = 80 booleans for γ.
  - Total: 152 booleans, 144 tensor-equality constraints.
"""
from z3 import (And, Bool, BoolVal, If, Not, Or, Solver, Sum,
                Xor, sat, unsat, set_param)
import sys
import time

# Import the library.
sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/hopcroft_kerr_2x3x2')
from library import STRASSEN_2x2


N_A = 6
N_B = 6
M   = 4


def target_tensor():
    """T[j][i_a][i_b] = 1 iff A[i_a]·B[i_b] contributes to C[j]."""
    T = [[[0] * N_B for _ in range(N_A)] for _ in range(M)]
    for i in range(2):
        for j in range(2):
            c_idx = i * 2 + j
            for k in range(3):
                a_idx = i * 3 + k
                b_idx = k * 2 + j
                T[c_idx][a_idx][b_idx] = 1
    return T


def strassen_effective_bilinear_forms():
    """For each of Strassen's 7 mults, compute its (L_a, L_b) as
    bilinear forms over the FULL 6-dim A and 6-dim B input space.

    A_left indices map to global A as:
        A_left[0]=a00 (gl 0), A_left[1]=a01 (gl 1),
        A_left[2]=a10 (gl 3), A_left[3]=a11 (gl 4).
    A_right entries (a02 gl 2, a12 gl 5) get 0 coefficient.

    Similarly for B_top (b00, b01, b10, b11 at gl 0, 1, 2, 3),
    B_bot (b20 gl 4, b21 gl 5) get 0.
    """
    # Map from Strassen-local index to global index.
    a_local_to_global = {0: 0, 1: 1, 2: 3, 3: 4}  # a00, a01, a10, a11
    b_local_to_global = {0: 0, 1: 1, 2: 2, 3: 3}  # b00, b01, b10, b11

    strassen_L_a_global = []
    strassen_L_b_global = []
    for k in range(STRASSEN_2x2["K"]):
        la = [0] * N_A
        lb = [0] * N_B
        for local_i in range(4):
            la[a_local_to_global[local_i]] = STRASSEN_2x2["L_a"][k][local_i]
            lb[b_local_to_global[local_i]] = STRASSEN_2x2["L_b"][k][local_i]
        strassen_L_a_global.append(la)
        strassen_L_b_global.append(lb)
    return strassen_L_a_global, strassen_L_b_global


def encode_search(K_extra, sym_break=True):
    """Build the K=7+K_extra search for 2×3 × 3×2 matrix mult."""
    solver = Solver()

    # Strassen's 7 mults give fixed L_a, L_b over the global 6-dim
    # A and 6-dim B input spaces.
    s_La, s_Lb = strassen_effective_bilinear_forms()
    K_strassen = STRASSEN_2x2["K"]
    K_total = K_strassen + K_extra

    # Extra mults: parametric ±1 coefficients via pos/neg flags.
    e_a_p = [[Bool(f"ea_p_{k}_{i}") for i in range(N_A)] for k in range(K_extra)]
    e_a_n = [[Bool(f"ea_n_{k}_{i}") for i in range(N_A)] for k in range(K_extra)]
    e_b_p = [[Bool(f"eb_p_{k}_{i}") for i in range(N_B)] for k in range(K_extra)]
    e_b_n = [[Bool(f"eb_n_{k}_{i}") for i in range(N_B)] for k in range(K_extra)]

    # Disallow (pos AND neg) per coefficient.
    for k in range(K_extra):
        for i in range(N_A):
            solver.add(Not(And(e_a_p[k][i], e_a_n[k][i])))
        for i in range(N_B):
            solver.add(Not(And(e_b_p[k][i], e_b_n[k][i])))

    # γ combiners (M outputs × K_total mults) ∈ {-1, 0, +1}.
    g_p = [[Bool(f"gp_{j}_{k}") for k in range(K_total)] for j in range(M)]
    g_n = [[Bool(f"gn_{j}_{k}") for k in range(K_total)] for j in range(M)]
    for j in range(M):
        for k in range(K_total):
            solver.add(Not(And(g_p[j][k], g_n[j][k])))

    # Build per-(k, i_a, i_b) coefficient of the bilinear product k.
    # For Strassen k ∈ [0, K_strassen): coefficient is product of
    # fixed L_a[k][i_a] · L_b[k][i_b], in {-1, 0, +1}.
    # For extra k ∈ [K_strassen, K_total): coefficient is determined
    # by (e_a_p, e_a_n, e_b_p, e_b_n) — boolean expressions.

    # Tensor equality constraint:
    # For each (j, i_a, i_b):
    #   Σ_k γ[j][k] · α[k][i_a] · β[k][i_b]  =  T[j][i_a][i_b]
    #
    # We use Z3 Int arithmetic for the sum (bounded, [-K_total, K_total]).
    # Each per-k term is in {-1, 0, +1}.
    T = target_tensor()
    for j in range(M):
        for ia in range(N_A):
            for ib in range(N_B):
                # γ[j][k] · α[k][ia] · β[k][ib] for each k.
                terms = []
                for k in range(K_strassen):
                    # Strassen: fixed product L_a[k][ia] · L_b[k][ib] in {-1, 0, +1}.
                    coeff_const = s_La[k][ia] * s_Lb[k][ib]
                    if coeff_const == 0:
                        continue
                    # γ[j][k] (in {-1, 0, +1}) times the constant.
                    # Use Int(γ) = (g_p ? 1 : 0) - (g_n ? 1 : 0).
                    gamma_val = If(g_p[j][k], 1, 0) - If(g_n[j][k], 1, 0)
                    terms.append(coeff_const * gamma_val)
                for k_ext in range(K_extra):
                    k = K_strassen + k_ext
                    # α[k][ia] = (e_a_p[k_ext][ia] ? 1 : 0) - (e_a_n[k_ext][ia] ? 1 : 0)
                    # β[k][ib] similar.
                    # γ[j][k] similar.
                    # Triple product over signed booleans.
                    # Encode as If-chain.
                    a_val = If(e_a_p[k_ext][ia], 1, 0) - If(e_a_n[k_ext][ia], 1, 0)
                    b_val = If(e_b_p[k_ext][ib], 1, 0) - If(e_b_n[k_ext][ib], 1, 0)
                    g_val = If(g_p[j][k], 1, 0) - If(g_n[j][k], 1, 0)
                    terms.append(g_val * a_val * b_val)
                if terms:
                    solver.add(Sum(terms) == T[j][ia][ib])
                else:
                    solver.add(T[j][ia][ib] == 0)

    # Each extra mult is non-trivial (α nonzero somewhere, β nonzero somewhere).
    for k in range(K_extra):
        solver.add(Or(*[Or(e_a_p[k][i], e_a_n[k][i]) for i in range(N_A)]))
        solver.add(Or(*[Or(e_b_p[k][i], e_b_n[k][i]) for i in range(N_B)]))
        # Each extra mult is USED by at least one output.
        solver.add(Or(*[Or(g_p[j][K_strassen + k], g_n[j][K_strassen + k])
                        for j in range(M)]))

    if sym_break and K_extra > 1:
        # Lex-order across the extra slots only (Strassen's 7 are
        # fixed/distinct).
        def sig(k):
            s = []
            for i in range(N_A):
                s += [e_a_p[k][i], e_a_n[k][i]]
            for i in range(N_B):
                s += [e_b_p[k][i], e_b_n[k][i]]
            for j in range(M):
                s += [g_p[j][K_strassen + k], g_n[j][K_strassen + k]]
            return s

        for k in range(K_extra - 1):
            sa, sb = sig(k), sig(k + 1)
            le_clauses = []
            for plen in range(len(sa)):
                eqs = And(*[sa[m] == sb[m] for m in range(plen)]) \
                      if plen > 0 else BoolVal(True)
                lt = And(Not(sa[plen]), sb[plen])
                le_clauses.append(And(eqs, lt))
            le_clauses.append(And(*[sa[m] == sb[m] for m in range(len(sa))]))
            solver.add(Or(*le_clauses))

    return solver, e_a_p, e_a_n, e_b_p, e_b_n, g_p, g_n


def extract(model, e_a_p, e_a_n, e_b_p, e_b_n, g_p, g_n,
            K_strassen, K_extra):
    def val(p, n):
        if bool(model[p]) and not bool(model[n]):
            return 1
        if bool(model[n]) and not bool(model[p]):
            return -1
        return 0
    K_total = K_strassen + K_extra
    M_ = len(g_p)
    extra_L_a = [[val(e_a_p[k][i], e_a_n[k][i]) for i in range(N_A)]
                 for k in range(K_extra)]
    extra_L_b = [[val(e_b_p[k][i], e_b_n[k][i]) for i in range(N_B)]
                 for k in range(K_extra)]
    gamma = [[val(g_p[j][k], g_n[j][k]) for k in range(K_total)]
             for j in range(M_)]
    return extra_L_a, extra_L_b, gamma


def verify(extra_L_a, extra_L_b, gamma, K_strassen, K_extra):
    """Symbolically verify the discovered algorithm."""
    s_La, s_Lb = strassen_effective_bilinear_forms()
    T = target_tensor()
    K_total = K_strassen + K_extra
    ok = True
    for j in range(M):
        for ia in range(N_A):
            for ib in range(N_B):
                acc = 0
                for k in range(K_strassen):
                    acc += gamma[j][k] * s_La[k][ia] * s_Lb[k][ib]
                for k_ext in range(K_extra):
                    acc += (gamma[j][K_strassen + k_ext]
                            * extra_L_a[k_ext][ia] * extra_L_b[k_ext][ib])
                if acc != T[j][ia][ib]:
                    print(f"  VERIFY-FAIL c[{j}], a[{ia}], b[{ib}]: "
                          f"got {acc}, expected {T[j][ia][ib]}")
                    ok = False
    return ok


def print_solution(extra_L_a, extra_L_b, gamma, K_strassen, K_extra):
    a_lbl = ["a00", "a01", "a02", "a10", "a11", "a12"]
    b_lbl = ["b00", "b01", "b10", "b11", "b20", "b21"]
    c_lbl = ["c00", "c01", "c10", "c11"]
    K_total = K_strassen + K_extra

    def vstr(vals, labels):
        parts = []
        for v, lbl in zip(vals, labels):
            if v == 1: parts.append(f"+{lbl}")
            elif v == -1: parts.append(f"-{lbl}")
        s = " ".join(parts)
        return s.lstrip("+").strip() if s else "0"

    print(f"\n=== K={K_total} algorithm for 2×3 × 3×2 ===")
    print(f"(Strassen 7-mult on A_left × B_top + {K_extra} extra "
          f"parametric rank-1 mults)")
    print(f"\nStrassen mults (fixed, library):")
    s_La, s_Lb = strassen_effective_bilinear_forms()
    for k in range(K_strassen):
        print(f"  m{k} = ({vstr(s_La[k], a_lbl)}) × ({vstr(s_Lb[k], b_lbl)})")
    print(f"\nExtra mults (search-discovered):")
    for k in range(K_extra):
        print(f"  m{K_strassen + k} = ({vstr(extra_L_a[k], a_lbl)}) "
              f"× ({vstr(extra_L_b[k], b_lbl)})")
    print()
    for j in range(M):
        terms = []
        for k in range(K_total):
            v = gamma[j][k]
            if v == 1: terms.append(f"+m{k}")
            elif v == -1: terms.append(f"-m{k}")
        s = " ".join(terms).lstrip("+").strip() or "0"
        print(f"  {c_lbl[j]} = {s}")


def search(K_extra, timeout_s=600, sym_break=True):
    set_param("parallel.enable", True)
    K_strassen = STRASSEN_2x2["K"]
    K_total = K_strassen + K_extra
    print(f"L1.2 speculation search:")
    print(f"  Strassen 2×2 K={K_strassen} on A_left × B_top (FIXED, "
          f"Lean-axiomatized).")
    print(f"  + {K_extra} extra parametric rank-1 mults over full (A, B).")
    print(f"  → Total K_total = {K_total} (vs published Hopcroft-Kerr 11).")
    if K_total < 11:
        print(f"  *** Would BEAT Hopcroft-Kerr if SAT. ***")
    print(f"  Timeout: {timeout_s}s.")
    sys.stdout.flush()

    solver, eap, ean, ebp, ebn, gp, gn = encode_search(K_extra, sym_break=sym_break)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    result = solver.check()
    elapsed = time.monotonic() - t0
    print(f"\n  Z3 result: {result}  ({elapsed:.1f}s)")
    sys.stdout.flush()

    if result == sat:
        model = solver.model()
        eLa, eLb, gamma = extract(model, eap, ean, ebp, ebn, gp, gn,
                                  K_strassen, K_extra)
        print_solution(eLa, eLb, gamma, K_strassen, K_extra)
        if verify(eLa, eLb, gamma, K_strassen, K_extra):
            print(f"\n  *** SAT, verified: K={K_total} for 2×3 × 3×2 over ℤ. ***")
            if K_total < 11:
                print(f"  *** BEATS Hopcroft-Kerr 1971.  Verify novelty "
                      f"vs Pan, Smirnov, etc.  Conditional on "
                      f"strassen_2x2_correct (Lean-verifiable). ***")
        return 0
    elif result == unsat:
        print(f"\n  *** UNSAT: 'Strassen + {K_extra} extras' cannot "
              f"achieve K={K_total}. ***")
        print(f"  Rules out THIS structural class.  Doesn't prove "
              f"R(2×3×2) > {K_total} in general.")
        return 0
    else:
        print(f"\n  *** TIMEOUT. ***")
        return 1


def main():
    K_extra = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    t = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    return search(K_extra, timeout_s=t)


if __name__ == "__main__":
    sys.exit(main())
