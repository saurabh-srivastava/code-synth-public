"""companion_bounds.py — verify R(2,1,3) = R(3,1,2) = 6.

These are outer-product-shaped sub-problems.  R(m,1,p) = mp
(naive is tight) — confirm via Z3 search at K=mp-1 (UNSAT
expected) and K=mp (SAT).
"""
from z3 import (And, Bool, BoolVal, If, Not, Or, Solver, Sum,
                Xor, sat, unsat, set_param)
import sys
import time


def encode_mat_mul(m, n, p, K, sym_break=True):
    """Bilinear rank search for m×n × n×p mat-mul at rank K
    using flat boolean encoding."""
    N_A = m * n
    N_B = n * p
    M_OUT = m * p
    solver = Solver()

    a_p = [[Bool(f"ap_{k}_{i}") for i in range(N_A)] for k in range(K)]
    a_n = [[Bool(f"an_{k}_{i}") for i in range(N_A)] for k in range(K)]
    b_p = [[Bool(f"bp_{k}_{i}") for i in range(N_B)] for k in range(K)]
    b_n = [[Bool(f"bn_{k}_{i}") for i in range(N_B)] for k in range(K)]
    g_p = [[Bool(f"gp_{j}_{k}") for k in range(K)] for j in range(M_OUT)]
    g_n = [[Bool(f"gn_{j}_{k}") for k in range(K)] for j in range(M_OUT)]

    for k in range(K):
        for i in range(N_A):
            solver.add(Not(And(a_p[k][i], a_n[k][i])))
        for i in range(N_B):
            solver.add(Not(And(b_p[k][i], b_n[k][i])))
        for j in range(M_OUT):
            solver.add(Not(And(g_p[j][k], g_n[j][k])))

    # Target tensor.
    T = [[[0] * N_B for _ in range(N_A)] for _ in range(M_OUT)]
    for i in range(m):
        for j in range(p):
            c_idx = i * p + j
            for k in range(n):
                T[c_idx][i * n + k][k * p + j] = 1

    for j in range(M_OUT):
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

    for k in range(K):
        solver.add(Or(*[Or(a_p[k][i], a_n[k][i]) for i in range(N_A)]))
        solver.add(Or(*[Or(b_p[k][i], b_n[k][i]) for i in range(N_B)]))
        solver.add(Or(*[Or(g_p[j][k], g_n[j][k]) for j in range(M_OUT)]))

    if sym_break:
        def sig(k):
            s = []
            for i in range(N_A):
                s += [a_p[k][i], a_n[k][i]]
            for i in range(N_B):
                s += [b_p[k][i], b_n[k][i]]
            for j in range(M_OUT):
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

    return solver


def search(m, n, p, K, timeout_s=60):
    set_param("parallel.enable", True)
    solver = encode_mat_mul(m, n, p, K)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    r = solver.check()
    el = time.monotonic() - t0
    return str(r), el


def main():
    cases = [
        # (m, n, p, K, expected, description)
        (2, 1, 3, 5, "unsat", "R(2,1,3) ≥ 6 (K=5 should UNSAT)"),
        (2, 1, 3, 6, "sat",   "R(2,1,3) ≤ 6 (K=6 should SAT naive)"),
        (3, 1, 2, 5, "unsat", "R(3,1,2) ≥ 6 (K=5 should UNSAT)"),
        (3, 1, 2, 6, "sat",   "R(3,1,2) ≤ 6 (K=6 should SAT naive)"),
    ]
    results = []
    for m, n, p, K, expected, desc in cases:
        print(f"  {desc} — running...", flush=True)
        verdict, t = search(m, n, p, K, timeout_s=120)
        results.append((m, n, p, K, expected, verdict, t))
        print(f"    Z3: {verdict} ({t:.2f}s)" +
              (f"  ✓ matches expected {expected}"
               if verdict == expected else
               f"  ✗ EXPECTED {expected}"))

    print("\n" + "=" * 70)
    print(f"{'(m,n,p,K)':<14} {'Expected':<10} {'Got':<10} {'Time':>10}")
    print("=" * 70)
    for m, n, p, K, exp, got, t in results:
        tag = "✓" if exp == got else "✗"
        print(f"({m},{n},{p}, K={K})    {exp:<10} {got:<10} {t:>8.2f}s  {tag}")


if __name__ == "__main__":
    main()
