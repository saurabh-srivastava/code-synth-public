"""gf2_polymul_search — parametric bilinear-rank search for
polynomial multiplication over GF(2)[x].

Generalizes `karatsuba_gf2_deg2_search5.py` to arbitrary degree
(N) and arbitrary multiplication count (K).  Direct Z3 SAT
encoding of the tensor decomposition.

Usage:
    python gf2_polymul_search.py N K [timeout_s]

For N inputs per polynomial (degree N-1), the product has
M = 2N-1 output coefficients.  Searches for a K-multiplication
algorithm via the bilinear-rank decomposition formulation.

Known results (Z3-checked):
    N=2 (deg-1): K=3 SAT, K=2 UNSAT.  Rank = 3.  (Karatsuba)
    N=3 (deg-2): K=6 SAT, K=5 UNSAT.  Rank = 6.  (Karatsuba-with-sharing)
    N=4 (deg-3): K=9 SAT, K=8 ??? (timeouts at 5min).  Rank ∈ [8, 9].
                  **K=8 is the next open question.**

For higher N, the search space grows; symmetry breaking + good
SMT preprocessing become critical.
"""
import sys
import time
from z3 import (And, Bool, BoolVal, Not, Or, Solver, Xor,
                sat, unsat, set_param)


def target_tensor(N):
    """T[j][i][i'] = 1 iff p_i·q_{i'} contributes to c_j."""
    M = 2 * N - 1
    T = [[[0] * N for _ in range(N)] for _ in range(M)]
    for j in range(M):
        for i in range(N):
            for ii in range(N):
                if i + ii == j:
                    T[j][i][ii] = 1
    return T


def xor_all(terms):
    if not terms:
        return BoolVal(False)
    acc = terms[0]
    for t in terms[1:]:
        acc = Xor(acc, t)
    return acc


def vec_lex_le(a, b):
    """a <= b lexicographically (False < True per index)."""
    result = BoolVal(False)
    eq_so_far = BoolVal(True)
    for ai, bi in zip(a, b):
        result = Or(result, And(eq_so_far, Not(ai), bi))
        eq_so_far = And(eq_so_far, ai == bi)
    return Or(result, And(*[ai == bi for ai, bi in zip(a, b)]))


def encode(solver, N, K, symmetry=True):
    M = 2 * N - 1
    alpha = [[Bool(f"a_{k}_{i}") for i in range(N)] for k in range(K)]
    beta  = [[Bool(f"b_{k}_{i}") for i in range(N)] for k in range(K)]
    gamma = [[Bool(f"g_{j}_{k}") for k in range(K)] for j in range(M)]

    T = target_tensor(N)

    # Tensor-equality constraints.
    for j in range(M):
        for i in range(N):
            for ii in range(N):
                terms = [And(gamma[j][k], alpha[k][i], beta[k][ii])
                         for k in range(K)]
                xor = xor_all(terms)
                if T[j][i][ii] == 1:
                    solver.add(xor)
                else:
                    solver.add(Not(xor))

    # Non-trivial mults.
    for k in range(K):
        solver.add(Or(*alpha[k]))
        solver.add(Or(*beta[k]))

    # Each mult used by at least one output.
    for k in range(K):
        solver.add(Or(*[gamma[j][k] for j in range(M)]))

    if symmetry:
        # Lex-order across mults by signature.
        for k in range(K - 1):
            sig_k   = alpha[k]   + beta[k]   + [gamma[j][k]   for j in range(M)]
            sig_kp1 = alpha[k+1] + beta[k+1] + [gamma[j][k+1] for j in range(M)]
            solver.add(vec_lex_le(sig_k, sig_kp1))

    return alpha, beta, gamma


def search(N, K, timeout_s=600, symmetry=True):
    M = 2 * N - 1
    set_param("parallel.enable", True)
    solver = Solver()
    solver.set("timeout", timeout_s * 1000)

    print(f"\nGF(2) deg-{N-1} × deg-{N-1} polymul rank search:")
    print(f"  K = {K} multiplications, N = {N} inputs/side, "
          f"M = {M} outputs")
    print(f"  Booleans: {K*N*2 + M*K}")
    print(f"  Tensor constraints: {M*N*N}")
    print(f"  Symmetry: {'lex-order + non-trivial + used' if symmetry else 'NONE'}")
    print(f"  Timeout: {timeout_s}s")

    alpha, beta, gamma = encode(solver, N, K, symmetry=symmetry)

    t0 = time.monotonic()
    result = solver.check()
    elapsed = time.monotonic() - t0
    print(f"\n  Z3 result: {result}  ({elapsed:.1f}s)")

    if result == sat:
        model = solver.model()
        print(f"\n=== {K}-multiplication algorithm (n={N}) ===")
        for k in range(K):
            a_bits = [int(bool(model[alpha[k][i]])) for i in range(N)]
            b_bits = [int(bool(model[beta[k][i]]))  for i in range(N)]
            a_str = " + ".join(f"p{i}" for i in range(N) if a_bits[i]) or "0"
            b_str = " + ".join(f"q{i}" for i in range(N) if b_bits[i]) or "0"
            print(f"  m{k} = ({a_str}) * ({b_str})")
        print()
        for j in range(M):
            used = [k for k in range(K) if bool(model[gamma[j][k]])]
            terms = " + ".join(f"m{k}" for k in used) or "0"
            print(f"  r{j} = ({terms}) mod 2")
        return 0
    elif result == unsat:
        print(f"\n*** {K}-mult IMPOSSIBLE for n={N} (Z3 SAT verdict). ***")
        print(f"   Bilinear rank ≥ {K+1} over GF(2).")
        return 0
    else:
        print(f"\n*** Z3 timeout at K={K}, n={N}.  Try longer "
              f"timeout, stronger encoding, or §G.5 IR work. ***")
        return 1


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        print("Defaults: N=4, K=8, timeout=600s.")
        N, K, T = 4, 8, 600
    else:
        N = int(sys.argv[1])
        K = int(sys.argv[2])
        T = int(sys.argv[3]) if len(sys.argv) > 3 else 600
    return search(N, K, timeout_s=T)


if __name__ == "__main__":
    sys.exit(main())
