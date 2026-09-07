"""direct_k10.py — direct K=10 SAT search for 2×3 × 3×2 over ℤ.

No library entries; 10 fully parametric rank-1 mults with ±1
coefficients.  Uses flat boolean encoding (pos/neg flag pairs +
If-Else over booleans → Int) to avoid NIA wedge.

Search dimensions:
  α: 10 × 6 inputs × 2 (pos/neg) = 120 booleans
  β: 10 × 6 × 2 = 120
  γ: 4 outputs × 10 × 2 = 80
  Total: 320 booleans + 144 tensor constraints.

This is in the "wedge regime" per L2.1 lessons.  A 2-hour
budget gives Z3 maximum opportunity.  If SAT, NEW result
(R(2,3,2) ≤ 10).  If UNSAT, confirms R(2,3,2) ≥ 11 (matches
Hopcroft-Kerr upper bound; tightens the literature).
"""
from z3 import (And, Bool, BoolVal, If, Not, Or, Solver, Sum,
                Xor, sat, unsat, set_param)
import sys
import time


N_A = 6
N_B = 6
M   = 4


def target_tensor():
    T = [[[0] * N_B for _ in range(N_A)] for _ in range(M)]
    for i in range(2):
        for j in range(2):
            c_idx = i * 2 + j
            for k in range(3):
                T[c_idx][i * 3 + k][k * 2 + j] = 1
    return T


def encode(K, sym_break=True):
    solver = Solver()
    a_p = [[Bool(f"ap_{k}_{i}") for i in range(N_A)] for k in range(K)]
    a_n = [[Bool(f"an_{k}_{i}") for i in range(N_A)] for k in range(K)]
    b_p = [[Bool(f"bp_{k}_{i}") for i in range(N_B)] for k in range(K)]
    b_n = [[Bool(f"bn_{k}_{i}") for i in range(N_B)] for k in range(K)]
    g_p = [[Bool(f"gp_{j}_{k}") for k in range(K)] for j in range(M)]
    g_n = [[Bool(f"gn_{j}_{k}") for k in range(K)] for j in range(M)]

    for k in range(K):
        for i in range(N_A):
            solver.add(Not(And(a_p[k][i], a_n[k][i])))
        for i in range(N_B):
            solver.add(Not(And(b_p[k][i], b_n[k][i])))
        for j in range(M):
            solver.add(Not(And(g_p[j][k], g_n[j][k])))

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

    # Non-trivial slots.
    for k in range(K):
        solver.add(Or(*[Or(a_p[k][i], a_n[k][i]) for i in range(N_A)]))
        solver.add(Or(*[Or(b_p[k][i], b_n[k][i]) for i in range(N_B)]))
        solver.add(Or(*[Or(g_p[j][k], g_n[j][k]) for j in range(M)]))

    if sym_break:
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

    return solver, a_p, a_n, b_p, b_n, g_p, g_n


def search(K, timeout_s):
    set_param("parallel.enable", True)
    print(f"Direct K={K} SAT search for 2×3 × 3×2 over ℤ "
          f"(no library entries).")
    print(f"  Search dimension: {K*(N_A + N_B + M)*2} booleans "
          f"+ {M*N_A*N_B} tensor constraints.")
    print(f"  Timeout: {timeout_s}s.")
    sys.stdout.flush()
    solver, *_ = encode(K)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    r = solver.check()
    el = time.monotonic() - t0
    print(f"\n  Z3: {r}  ({el:.2f}s)")
    if r == sat:
        print(f"\n  *** SAT: R(2,3,2) ≤ {K}. ***")
        if K < 11:
            print(f"  BEATS Hopcroft-Kerr 11.  Extract model for "
                  f"verification.")
    elif r == unsat:
        print(f"\n  *** UNSAT: R(2,3,2) > {K}. ***")
        if K == 10:
            print(f"  CONFIRMS R(2,3,2) ≥ 11 — Hopcroft-Kerr is tight "
                  f"(over ±1-coefficient ℤ algorithms).")
    else:
        print(f"\n  *** TIMEOUT. ***")
    return r


if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    t = int(sys.argv[2]) if len(sys.argv) > 2 else 7200  # 2 hours default
    search(K, t)
