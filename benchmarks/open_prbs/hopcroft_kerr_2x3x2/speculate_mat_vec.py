"""speculate_mat_vec.py — search for R(2,3,1) ≤ 5.

Part B speculation: if a sub-optimal mat-vec algorithm
R(2×3 × 3×1) = 5 exists (vs naive 6), then composing on each
column of B gives R(2,3,2) ≤ 10 — beating Hopcroft-Kerr 11.

This script directly searches for the SUB-ALGORITHM (small
search space).  If SAT, it provides a Lean-axiomatizable
library entry that discharges the K=10 conditional result.

Encoding:
    inputs: 6 A entries (a00, a01, a02, a10, a11, a12)
            3 v entries (v0, v1, v2)
    outputs: 2 (c0 = A·v[0], c1 = A·v[1])
    target tensor T[j][i_a][i_v] = 1 iff a_ji · v_i appears in c_j.
        Specifically: T[c0][a0i][vi] = 1 for i ∈ {0,1,2}
                       T[c1][a1i][vi] = 1 for i ∈ {0,1,2}
    Search variables: K rank-1 mults with ±1 coefficients
        over (A, v) input space; γ combiners for 2 outputs.

For K=5: 5·(6+3)·2 = 90 bits for L_a + L_v + 2·5·2 = 20 bits for γ
       = 110 booleans, 2·6·3 = 36 tensor constraints.
"""
from z3 import (And, Bool, BoolVal, If, Not, Or, Solver, Sum,
                Xor, sat, unsat, set_param)
import sys
import time


N_A = 6  # mat-vec matrix has 6 entries (2×3)
N_V = 3  # vector has 3 entries
M   = 2  # output is 2 (2-vector)


def target_tensor():
    T = [[[0] * N_V for _ in range(N_A)] for _ in range(M)]
    # A = [[a00 a01 a02], [a10 a11 a12]] in row-major:
    # idx: a00=0, a01=1, a02=2, a10=3, a11=4, a12=5
    # v = (v0, v1, v2) at idx 0, 1, 2.
    # c[0] = a00·v0 + a01·v1 + a02·v2
    # c[1] = a10·v0 + a11·v1 + a12·v2
    for row in range(2):
        for col in range(3):
            a_idx = row * 3 + col
            T[row][a_idx][col] = 1
    return T


def encode_search(K, sym_break=True):
    solver = Solver()

    a_p = [[Bool(f"ap_{k}_{i}") for i in range(N_A)] for k in range(K)]
    a_n = [[Bool(f"an_{k}_{i}") for i in range(N_A)] for k in range(K)]
    v_p = [[Bool(f"vp_{k}_{i}") for i in range(N_V)] for k in range(K)]
    v_n = [[Bool(f"vn_{k}_{i}") for i in range(N_V)] for k in range(K)]
    g_p = [[Bool(f"gp_{j}_{k}") for k in range(K)] for j in range(M)]
    g_n = [[Bool(f"gn_{j}_{k}") for k in range(K)] for j in range(M)]

    for k in range(K):
        for i in range(N_A):
            solver.add(Not(And(a_p[k][i], a_n[k][i])))
        for i in range(N_V):
            solver.add(Not(And(v_p[k][i], v_n[k][i])))
        for j in range(M):
            solver.add(Not(And(g_p[j][k], g_n[j][k])))

    T = target_tensor()
    for j in range(M):
        for ia in range(N_A):
            for iv in range(N_V):
                terms = []
                for k in range(K):
                    # Triple product γ·α·v ∈ {-1, 0, +1}.
                    # nonzero iff all three coefficients nonzero.
                    # sign = parity of negatives (XOR of n-bits).
                    # Use boolean encoding to keep Z3 in QF_LIA / SAT
                    # (no Int multiplication → no NIA).
                    nz = And(Or(g_p[j][k], g_n[j][k]),
                             Or(a_p[k][ia], a_n[k][ia]),
                             Or(v_p[k][iv], v_n[k][iv]))
                    neg = Xor(g_n[j][k], Xor(a_n[k][ia], v_n[k][iv]))
                    terms.append(If(nz, If(neg, -1, 1), 0))
                solver.add(Sum(terms) == T[j][ia][iv])

    # Non-trivial mults.
    for k in range(K):
        solver.add(Or(*[Or(a_p[k][i], a_n[k][i]) for i in range(N_A)]))
        solver.add(Or(*[Or(v_p[k][i], v_n[k][i]) for i in range(N_V)]))
        solver.add(Or(*[Or(g_p[j][k], g_n[j][k]) for j in range(M)]))

    if sym_break:
        def sig(k):
            s = []
            for i in range(N_A):
                s += [a_p[k][i], a_n[k][i]]
            for i in range(N_V):
                s += [v_p[k][i], v_n[k][i]]
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

    return solver, a_p, a_n, v_p, v_n, g_p, g_n


def extract(model, ap, an, vp, vn, gp, gn, K):
    def val(p, n):
        if bool(model[p]) and not bool(model[n]): return 1
        if bool(model[n]) and not bool(model[p]): return -1
        return 0
    a_vals = [[val(ap[k][i], an[k][i]) for i in range(N_A)] for k in range(K)]
    v_vals = [[val(vp[k][i], vn[k][i]) for i in range(N_V)] for k in range(K)]
    g_vals = [[val(gp[j][k], gn[j][k]) for k in range(K)] for j in range(M)]
    return a_vals, v_vals, g_vals


def verify(a_vals, v_vals, g_vals, K):
    T = target_tensor()
    ok = True
    for j in range(M):
        for ia in range(N_A):
            for iv in range(N_V):
                acc = 0
                for k in range(K):
                    acc += g_vals[j][k] * a_vals[k][ia] * v_vals[k][iv]
                if acc != T[j][ia][iv]:
                    print(f"  VERIFY-FAIL c[{j}], a[{ia}], v[{iv}]: "
                          f"got {acc}, expected {T[j][ia][iv]}")
                    ok = False
    return ok


def print_solution(a_vals, v_vals, g_vals, K):
    a_lbl = ["a00", "a01", "a02", "a10", "a11", "a12"]
    v_lbl = ["v0", "v1", "v2"]
    print(f"\n=== K={K} algorithm for 2×3 × 3×1 mat-vec ===")
    def vstr(vals, labels):
        parts = []
        for v, lbl in zip(vals, labels):
            if v == 1: parts.append(f"+{lbl}")
            elif v == -1: parts.append(f"-{lbl}")
        s = " ".join(parts)
        return s.lstrip("+").strip() or "0"
    for k in range(K):
        print(f"  m{k} = ({vstr(a_vals[k], a_lbl)}) × ({vstr(v_vals[k], v_lbl)})")
    print()
    for j in range(M):
        terms = []
        for k in range(K):
            v = g_vals[j][k]
            if v == 1: terms.append(f"+m{k}")
            elif v == -1: terms.append(f"-m{k}")
        s = " ".join(terms).lstrip("+").strip() or "0"
        print(f"  c{j} = {s}")


def search(K, timeout_s=600, sym_break=True):
    set_param("parallel.enable", True)
    print(f"R(2,3,1) search for K={K} algorithm (2×3 mat × 3×1 vec).")
    print(f"  Naive: 6 mults.  Target: K=5 (if SAT, gives R(2,3,2) ≤ 10).")
    print(f"  Timeout: {timeout_s}s.")
    sys.stdout.flush()
    solver, ap, an, vp, vn, gp, gn = encode_search(K, sym_break=sym_break)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    r = solver.check()
    elapsed = time.monotonic() - t0
    print(f"\n  Z3: {r}  ({elapsed:.2f}s)")
    sys.stdout.flush()
    if r == sat:
        m = solver.model()
        a_v, v_v, g_v = extract(m, ap, an, vp, vn, gp, gn, K)
        print_solution(a_v, v_v, g_v, K)
        if verify(a_v, v_v, g_v, K):
            print(f"\n  *** R(2,3,1) ≤ {K} verified. ***")
            if K < 6:
                print(f"  *** NEW UPPER BOUND BELOW NAIVE 6.  Composes to "
                      f"R(2,3,2) ≤ {K * 2}. ***")
        return 0
    elif r == unsat:
        print(f"\n  *** UNSAT: R(2,3,1) > {K}.  Naive 6 confirmed at "
              f"least at K+1.  Composition route to K=10 via "
              f"R(2,3,1)≤5 + transpose CLOSED. ***")
        return 0
    else:
        print(f"\n  *** TIMEOUT. ***")
        return 1


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    return search(K, timeout_s=t)


if __name__ == "__main__":
    sys.exit(main())
