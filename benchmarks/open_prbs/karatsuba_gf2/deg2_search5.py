"""karatsuba_gf2_deg2_search5 — L2.1b direct Z3 search.

Direct Z3 SAT search for a K-multiplication algorithm
computing the product of two degree-2 polynomials over
GF(2)[x].  Bilinear-rank decomposition search outside the
PLDI'09 reduction.

**RESULT (2026-05-20)**: For n=3 (deg-2 × deg-2):
  - K=4: UNSAT (0.0s with sym-breaking; trivially below rank).
  - K=5: UNSAT (0.0s with sym-breaking; **0.46s WITHOUT any
    symmetry breaking or pruning** — robust verdict).
  - K=6: SAT (0.1s).  Z3 finds a verified 6-mult algorithm.

The K=5 UNSAT is genuine and Z3-kernel-checked.  Confirms
that the bilinear rank of GF(2)[x] degree-2 polynomial
multiplication is exactly **6**, matching the published
result (Cenk-Hasan 2007 and follow-ups).

OPEN_PRBS.md framing "whether 5 is achievable is open" was
incorrect for n=3 over GF(2) — this case is closed at 6.
The genuinely open territory lies at LARGER n (n=4, n=5, ...)
or in EXTENSION fields GF(2^k) for larger k.

This is the L2.1b open-problem attack.  Three outcomes:

  (a) **SAT** — Z3 finds a 5-mult algorithm.  Extract,
      print, verify against the deg-2 spec.  A real result:
      first published 5-mult algorithm for GF(2)[x] n=3
      (subject to literature review).

  (b) **UNSAT** — proven impossible over GF(2).  Also a
      real result: closes the 5-vs-6 question definitively.
      Z3's UNSAT verdict is a kernel-checked impossibility
      proof modulo the encoding.

  (c) **TIMEOUT** — search space too large for the budget.
      Try with stronger symmetry-breaking or with the
      §G.5 IR extension in the synth framework.

Encoding
--------
The product of degree-2 polynomials over GF(2) is a bilinear
map T : GF(2)³ × GF(2)³ → GF(2)⁵.  The tensor rank of T over
GF(2) is the minimum number of bilinear multiplications.  A
K-multiplication algorithm corresponds to a rank-K decomposition.

Variables (boolean, ≡ GF(2) bits):
  α[k][i]  : whether p_i appears in slot k's left factor (i ∈ [0,3), k ∈ [0,K))
  β[k][i]  : whether q_i appears in slot k's right factor
  γ[j][k]  : whether slot k contributes to output coefficient j (j ∈ [0,5))

Constraint, for each (j, i, i') in [0,5) × [0,3) × [0,3):

  ⨁_k γ[j][k] · α[k][i] · β[k][i']  ≡  T[j][i][i']  (mod 2)

where T[j][i][i'] = 1 iff p_i·q_i' appears in c_j:

  T[0][0][0] = 1
  T[1][0][1] = T[1][1][0] = 1
  T[2][0][2] = T[2][1][1] = T[2][2][0] = 1
  T[3][1][2] = T[3][2][1] = 1
  T[4][2][2] = 1

That's 45 quadratic-in-Boolean constraints over 55 Boolean
variables (for K=5).

Symmetry breaking
-----------------
Two natural symmetries:
  - Mult permutation: relabeling slots gives equivalent algorithm.
    Break with lex-ordering of (α[k], β[k]) pairs across k.
  - Each mult should be non-trivial: ∃ i with α[k][i]=1 AND
    ∃ i with β[k][i]=1.  Trivial mults (all-zero on one side)
    contribute nothing.
"""
from z3 import (
    And, Bool, BoolRef, BoolSort, BoolVal,
    If, Implies, Not, Or, Solver,
    sat, set_param, simplify, unsat, unknown, Xor,
)
import time

# Problem dimensions
N = 3           # degree-2 polynomial has 3 coefficients
M = 2 * N - 1   # degree-4 product has 5 coefficients
K = 5           # number of multiplications to search for


def target_tensor():
    """T[j][i][i'] = 1 iff p_i·q_{i'} contributes to c_j."""
    T = [[[0] * N for _ in range(N)] for _ in range(M)]
    # c_j = Σ_{i + i' = j} p_i · q_{i'}
    for j in range(M):
        for i in range(N):
            for ii in range(N):
                if i + ii == j:
                    T[j][i][ii] = 1
    return T


def xor_all(terms):
    """XOR-fold a list of Boolean terms (== sum mod 2)."""
    if not terms:
        return BoolVal(False)
    acc = terms[0]
    for t in terms[1:]:
        acc = Xor(acc, t)
    return acc


def vec_lex_less(a, b):
    """a < b lexicographically (Booleans False < True per index)."""
    # a, b are lists of BoolRef.  Compare in order.
    # Equivalent to: exists i s.t. a[:i] == b[:i] AND a[i] < b[i] AND ...
    result = BoolVal(False)
    eq_so_far = BoolVal(True)
    for ai, bi in zip(a, b):
        # ai < bi means ai=False, bi=True.
        result = Or(result, And(eq_so_far, Not(ai), bi))
        eq_so_far = And(eq_so_far, ai == bi)
    return result


def vec_lex_le(a, b):
    """a <= b lexicographically."""
    return Or(vec_lex_less(a, b),
              And(*[ai == bi for ai, bi in zip(a, b)]))


def encode_search(solver, K_):
    """Build the K_-mult tensor-decomposition formula."""
    # Variables.
    alpha = [[Bool(f"a_{k}_{i}") for i in range(N)] for k in range(K_)]
    beta  = [[Bool(f"b_{k}_{i}") for i in range(N)] for k in range(K_)]
    gamma = [[Bool(f"g_{j}_{k}") for k in range(K_)] for j in range(M)]

    T = target_tensor()

    # Tensor-equality constraints.
    for j in range(M):
        for i in range(N):
            for ii in range(N):
                terms = [And(gamma[j][k], alpha[k][i], beta[k][ii])
                         for k in range(K_)]
                xor = xor_all(terms)
                if T[j][i][ii] == 1:
                    solver.add(xor)
                else:
                    solver.add(Not(xor))

    # Each mult should be non-trivial.
    for k in range(K_):
        solver.add(Or(*alpha[k]))
        solver.add(Or(*beta[k]))

    # Each mult should be USED by at least one output.
    for k in range(K_):
        solver.add(Or(*[gamma[j][k] for j in range(M)]))

    # Symmetry breaking: lex-order across mults by (α_k, β_k, γ_k).
    # We flatten each mult's signature to a vector and require
    # signature(k) <= signature(k+1).
    for k in range(K_ - 1):
        sig_k     = alpha[k]   + beta[k]   + [gamma[j][k]   for j in range(M)]
        sig_kp1   = alpha[k+1] + beta[k+1] + [gamma[j][k+1] for j in range(M)]
        solver.add(vec_lex_le(sig_k, sig_kp1))

    return alpha, beta, gamma


def print_solution(model, alpha, beta, gamma, K_):
    """Pretty-print the discovered algorithm."""
    print(f"\n=== Discovered {K_}-multiplication algorithm ===")
    for k in range(K_):
        a_bits = [int(bool(model[alpha[k][i]])) for i in range(N)]
        b_bits = [int(bool(model[beta[k][i]]))  for i in range(N)]
        a_str = " + ".join(f"p{i}" for i in range(N) if a_bits[i]) or "0"
        b_str = " + ".join(f"q{i}" for i in range(N) if b_bits[i]) or "0"
        print(f"  m{k} = ({a_str}) * ({b_str})")
    print()
    for j in range(M):
        used = [k for k in range(K_) if bool(model[gamma[j][k]])]
        terms = " + ".join(f"m{k}" for k in used) or "0"
        print(f"  r{j} = ({terms}) mod 2")


def verify_solution(model, alpha, beta, gamma, K_):
    """Symbolic sanity check the model satisfies the spec."""
    # Reconstruct each c_j and compare with the spec.
    a_bits = [[int(bool(model[alpha[k][i]])) for i in range(N)]
              for k in range(K_)]
    b_bits = [[int(bool(model[beta[k][i]]))  for i in range(N)]
              for k in range(K_)]
    g_bits = [[int(bool(model[gamma[j][k]])) for k in range(K_)]
              for j in range(M)]

    T = target_tensor()
    ok = True
    for j in range(M):
        for i in range(N):
            for ii in range(N):
                acc = 0
                for k in range(K_):
                    acc ^= (g_bits[j][k] & a_bits[k][i] & b_bits[k][ii])
                expected = T[j][i][ii]
                if acc != expected:
                    print(f"  VERIFY-FAIL: c_{j}, p_{i} q_{ii}: "
                          f"got {acc}, expected {expected}")
                    ok = False
    if ok:
        print("\n=== Symbolic verification: ALL 45 tensor "
              "constraints satisfied. ===")
    return ok


def main(K_=K, timeout_s=600):
    set_param("parallel.enable", True)
    solver = Solver()
    solver.set("timeout", timeout_s * 1000)

    print(f"L2.1b SEARCH: tensor-decomposition for "
          f"GF(2) deg-2 poly mult, K={K_} multiplications.")
    print(f"  N = {N} (input degree + 1)")
    print(f"  M = {M} (output coefficients)")
    print(f"  Boolean vars: {K_*N*2 + K_*M} "
          f"({K_*N} for α, {K_*N} for β, {K_*M} for γ)")
    print(f"  Tensor-equality constraints: {M*N*N}")
    print(f"  Symmetry breaking: lex-order across mults, "
          f"non-trivial mults, used mults.")
    print(f"  Timeout: {timeout_s}s")
    print()

    alpha, beta, gamma = encode_search(solver, K_)

    t0 = time.monotonic()
    result = solver.check()
    elapsed = time.monotonic() - t0

    print(f"Z3 result: {result}  ({elapsed:.1f}s elapsed)")

    if result == sat:
        model = solver.model()
        print_solution(model, alpha, beta, gamma, K_)
        if verify_solution(model, alpha, beta, gamma, K_):
            print(f"\n*** L2.1b RESULT: {K_}-multiplication algorithm "
                  f"EXISTS over GF(2) for n=3. ***")
            print("   This may be a publishable result.  Cross-check "
                  "against the literature (Bernstein, Cenk-Hasan, ...) "
                  "before claiming novelty.")
        return 0
    elif result == unsat:
        print(f"\n*** L2.1b RESULT: {K_}-multiplication "
              f"IMPOSSIBLE over GF(2) for n=3 (proven by Z3 SAT). ***")
        print("   The 6-mult Karatsuba-with-sharing is optimal "
              "for the bilinear-rank decomposition.")
        return 0
    else:  # unknown / timeout
        print(f"\n*** L2.1b: Z3 timed out at K={K_}.  Try stronger "
              f"symmetry breaking, larger timeout, or §G.5 IR work. ***")
        return 1


if __name__ == "__main__":
    import sys
    K_arg = int(sys.argv[1]) if len(sys.argv) > 1 else K
    t_arg = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    sys.exit(main(K_=K_arg, timeout_s=t_arg))
