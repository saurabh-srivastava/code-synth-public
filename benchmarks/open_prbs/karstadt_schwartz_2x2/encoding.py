"""encoding.py — shared Z3 encoding for K=7 ±1-coefficient 2×2 matmul.

Indexing convention:
  A entries (left matrix, row-major): a, b, c, d  →  0, 1, 2, 3
                                       A = [[a b], [c d]]
  B entries (right matrix, row-major): e, f, g, h  →  0, 1, 2, 3
                                       B = [[e f], [g h]]
  C entries (output, row-major):       c00, c01, c10, c11  →  0, 1, 2, 3
                                       C = A·B

Standard matmul:
  c00 = a·e + b·g       T[0][0][0] = T[0][1][2] = 1
  c01 = a·f + b·h       T[1][0][1] = T[1][1][3] = 1
  c10 = c·e + d·g       T[2][2][0] = T[2][3][2] = 1
  c11 = c·f + d·h       T[3][2][1] = T[3][3][3] = 1

Bilinear decomposition at rank K:
  m_k = (Σ_i α[k][i] · A_i) × (Σ_i β[k][i] · B_i)    α, β ∈ {-1, 0, +1}
  C_j = Σ_k γ[j][k] · m_k                            γ ∈ {-1, 0, +1}

Tensor identity (per j, ia, ib):
  T[j][ia][ib] == Σ_k γ[j][k] · α[k][ia] · β[k][ib]

The flat-boolean encoding represents each {-1, 0, +1} value with
two booleans (pos, neg) constrained disjoint.  Triple products
are computed without Int multiplication via:
    nz = (γ nonzero) ∧ (α nonzero) ∧ (β nonzero)
    neg = γ_neg XOR α_neg XOR β_neg
    contribution = If(nz, If(neg, -1, 1), 0)

This avoids Z3's NIA wedge.
"""
from z3 import (And, Bool, BoolVal, If, Not, Or, Solver, Optimize,
                Sum, Xor, sat, unsat)

N_A = 4    # |{a, b, c, d}|
N_B = 4    # |{e, f, g, h}|
M   = 4    # |{c00, c01, c10, c11}|


def target_tensor():
    """The 2×2 × 2×2 matrix-multiplication tensor."""
    T = [[[0] * N_B for _ in range(N_A)] for _ in range(M)]
    for i in range(2):           # row of C / A
        for j in range(2):       # col of C / B
            c_idx = i * 2 + j
            for k in range(2):   # inner index
                a_idx = i * 2 + k
                b_idx = k * 2 + j
                T[c_idx][a_idx][b_idx] = 1
    return T


def make_vars(K, prefix=""):
    """Allocate pos/neg booleans for α (K × N_A), β (K × N_B), γ (M × K)."""
    a_p = [[Bool(f"{prefix}ap_{k}_{i}") for i in range(N_A)] for k in range(K)]
    a_n = [[Bool(f"{prefix}an_{k}_{i}") for i in range(N_A)] for k in range(K)]
    b_p = [[Bool(f"{prefix}bp_{k}_{i}") for i in range(N_B)] for k in range(K)]
    b_n = [[Bool(f"{prefix}bn_{k}_{i}") for i in range(N_B)] for k in range(K)]
    g_p = [[Bool(f"{prefix}gp_{j}_{k}") for k in range(K)] for j in range(M)]
    g_n = [[Bool(f"{prefix}gn_{j}_{k}") for k in range(K)] for j in range(M)]
    return a_p, a_n, b_p, b_n, g_p, g_n


def add_disjoint(solver, a_p, a_n, b_p, b_n, g_p, g_n, K):
    """Each position has at most one of pos/neg set."""
    for k in range(K):
        for i in range(N_A):
            solver.add(Not(And(a_p[k][i], a_n[k][i])))
        for i in range(N_B):
            solver.add(Not(And(b_p[k][i], b_n[k][i])))
    for j in range(M):
        for k in range(K):
            solver.add(Not(And(g_p[j][k], g_n[j][k])))


def add_tensor_constraints(solver, a_p, a_n, b_p, b_n, g_p, g_n, K):
    """For each (j, ia, ib): T[j][ia][ib] == Σ_k γ·α·β."""
    T = target_tensor()
    for j in range(M):
        for ia in range(N_A):
            for ib in range(N_B):
                terms = []
                for k in range(K):
                    nz = And(Or(g_p[j][k], g_n[j][k]),
                             Or(a_p[k][ia], a_n[k][ia]),
                             Or(b_p[k][ib], b_n[k][ib]))
                    neg = Xor(g_n[j][k], Xor(a_n[k][ia], b_n[k][ib]))
                    terms.append(If(nz, If(neg, -1, 1), 0))
                solver.add(Sum(terms) == T[j][ia][ib])


def add_nontrivial(solver, a_p, a_n, b_p, b_n, g_p, g_n, K):
    """Each m_k must have ≥1 nonzero α coef, ≥1 nonzero β coef,
    and be used in ≥1 output (≥1 nonzero γ)."""
    for k in range(K):
        solver.add(Or(*[Or(a_p[k][i], a_n[k][i]) for i in range(N_A)]))
        solver.add(Or(*[Or(b_p[k][i], b_n[k][i]) for i in range(N_B)]))
        solver.add(Or(*[Or(g_p[j][k], g_n[j][k]) for j in range(M)]))
    # Each output must use ≥1 mult.
    for j in range(M):
        solver.add(Or(*[Or(g_p[j][k], g_n[j][k]) for k in range(K)]))


def add_sym_break(solver, a_p, a_n, b_p, b_n, g_p, g_n, K):
    """Lexicographic ordering on m_k by their full coefficient signature
    to break the K! permutation symmetry."""
    def sig(k):
        s = []
        for i in range(N_A):
            s += [a_p[k][i], a_n[k][i]]
        for i in range(N_B):
            s += [b_p[k][i], b_n[k][i]]
        for j in range(M):
            s += [g_p[j][k], g_n[j][k]]
        return s
    for k in range(K - 1):
        sa, sb = sig(k), sig(k + 1)
        le_clauses = []
        for plen in range(len(sa)):
            eqs = And(*[sa[m] == sb[m] for m in range(plen)]) \
                  if plen > 0 else BoolVal(True)
            lt = And(Not(sa[plen]), sb[plen])
            le_clauses.append(And(eqs, lt))
        le_clauses.append(And(*[sa[m] == sb[m] for m in range(len(sa))]))
        solver.add(Or(*le_clauses))


def nonzero_count_expr(a_p, a_n, b_p, b_n, g_p, g_n, K):
    """Returns a Sum() expression counting the total number of
    nonzero positions across α, β, γ."""
    terms = []
    for k in range(K):
        for i in range(N_A):
            terms.append(If(Or(a_p[k][i], a_n[k][i]), 1, 0))
        for i in range(N_B):
            terms.append(If(Or(b_p[k][i], b_n[k][i]), 1, 0))
    for j in range(M):
        for k in range(K):
            terms.append(If(Or(g_p[j][k], g_n[j][k]), 1, 0))
    return Sum(terms)


def additions_from_nonzeros(nz_count, K):
    """Convert total nonzero count to total addition count.
    K linear forms on left (each contributes |α_k|-1 adds),
    K on right (|β_k|-1), M outputs (|γ_j|-1).
    Sum = Σ|nz| - (2K + M)."""
    return nz_count - (2 * K + M)


def extract_model(model, a_p, a_n, b_p, b_n, g_p, g_n, K):
    """Return α, β, γ as lists of {-1, 0, +1} from a Z3 model."""
    def val(pv, nv):
        p = model[pv]
        n = model[nv]
        pp = bool(p) if p is not None else False
        nn = bool(n) if n is not None else False
        if pp and not nn:
            return 1
        if nn and not pp:
            return -1
        return 0
    alpha = [[val(a_p[k][i], a_n[k][i]) for i in range(N_A)] for k in range(K)]
    beta  = [[val(b_p[k][i], b_n[k][i]) for i in range(N_B)] for k in range(K)]
    gamma = [[val(g_p[j][k], g_n[j][k]) for k in range(K)] for j in range(M)]
    return alpha, beta, gamma


def verify_witness(alpha, beta, gamma, K):
    """Pure-Python cross-check: does this (α, β, γ) compute the matmul tensor?"""
    T = target_tensor()
    for j in range(M):
        for ia in range(N_A):
            for ib in range(N_B):
                acc = 0
                for k in range(K):
                    acc += gamma[j][k] * alpha[k][ia] * beta[k][ib]
                if acc != T[j][ia][ib]:
                    return False, (j, ia, ib, acc, T[j][ia][ib])
    return True, None


def count_nonzeros(alpha, beta, gamma):
    nz = 0
    for row in alpha: nz += sum(1 for v in row if v != 0)
    for row in beta:  nz += sum(1 for v in row if v != 0)
    for row in gamma: nz += sum(1 for v in row if v != 0)
    return nz


_A_LBL = ["a", "b", "c", "d"]
_B_LBL = ["e", "f", "g", "h"]
_C_LBL = ["c00", "c01", "c10", "c11"]


def _lc_str(vals, labels):
    parts = []
    for v, lbl in zip(vals, labels):
        if v == 1:
            parts.append(f"+ {lbl}" if parts else lbl)
        elif v == -1:
            parts.append(f"- {lbl}")
    if not parts:
        return "0"
    return " ".join(parts)


def print_witness(alpha, beta, gamma, K, label=""):
    if label:
        print(f"\n=== {label} ===")
    print(f"  K = {K} multiplications")
    nz = count_nonzeros(alpha, beta, gamma)
    print(f"  Σ|nz| = {nz}  →  additions = {nz - (2*K + M)}")
    print()
    for k in range(K):
        l_str = _lc_str(alpha[k], _A_LBL)
        r_str = _lc_str(beta[k], _B_LBL)
        print(f"  m{k} = ({l_str}) · ({r_str})")
    print()
    for j in range(M):
        gvals = gamma[j]
        m_lbls = [f"m{k}" for k in range(K)]
        c_str = _lc_str(gvals, m_lbls)
        print(f"  {_C_LBL[j]} = {c_str}")
