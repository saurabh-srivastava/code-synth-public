"""library_builder.py — Part A: build a library of low-rung
polymul decompositions over GF(2).

Runs direct Z3 SAT at many (n, K) configurations with 2-min
budgets.  Each SAT result yields a concrete (L_a, L_b, γ)
bilinear-rank decomposition.  Saves to `library.json` for use
by the larger-problem search (`library_search.py`).

Usage:
    python library_builder.py                  # build library
    python library_builder.py --multi N        # N models per (n,K)

The library is a JSON file with entries:
  {
    "name": "polymul_n_K_idx",
    "n": int, "K": int,
    "L_a": list[list[int]],   # K rows × n cols
    "L_b": list[list[int]],
    "gamma": list[list[int]], # (2n-1) rows × K cols
  }
"""
from z3 import (And, Bool, BoolVal, Not, Or, Solver, Xor,
                sat, unsat, set_param)
import json
import os
import sys
import time
from pathlib import Path


HERE = Path(__file__).parent
LIBRARY_PATH = HERE / "library.json"


def target_tensor(n):
    """T[j][i][k] = 1 iff a_i·b_k contributes to polymul_n output j."""
    M = 2 * n - 1
    T = [[[0] * n for _ in range(n)] for _ in range(M)]
    for j in range(M):
        for i in range(n):
            for k in range(n):
                if i + k == j:
                    T[j][i][k] = 1
    return T


def xor_all(terms):
    if not terms:
        return BoolVal(False)
    acc = terms[0]
    for t in terms[1:]:
        acc = Xor(acc, t)
    return acc


def vec_lex_le(a, b):
    result = BoolVal(False)
    eq_so_far = BoolVal(True)
    for ai, bi in zip(a, b):
        result = Or(result, And(eq_so_far, Not(ai), bi))
        eq_so_far = And(eq_so_far, ai == bi)
    return Or(result, And(*[ai == bi for ai, bi in zip(a, b)]))


def encode_search(n, K, sym_break=True):
    """Build the bilinear-rank K-decomposition formula for polymul_n."""
    M = 2 * n - 1
    alpha = [[Bool(f"a_{k}_{i}") for i in range(n)] for k in range(K)]
    beta  = [[Bool(f"b_{k}_{i}") for i in range(n)] for k in range(K)]
    gamma = [[Bool(f"g_{j}_{k}") for k in range(K)] for j in range(M)]

    solver = Solver()
    T = target_tensor(n)

    # Tensor equalities.
    for j in range(M):
        for i in range(n):
            for ii in range(n):
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

    # Each mult used.
    for k in range(K):
        solver.add(Or(*[gamma[j][k] for j in range(M)]))

    if sym_break:
        for k in range(K - 1):
            sig_k   = alpha[k]   + beta[k]   + [gamma[j][k]   for j in range(M)]
            sig_kp1 = alpha[k+1] + beta[k+1] + [gamma[j][k+1] for j in range(M)]
            solver.add(vec_lex_le(sig_k, sig_kp1))

    return solver, alpha, beta, gamma


def extract_model(model, alpha, beta, gamma, n, K):
    """Pull (L_a, L_b, γ) ints out of a Z3 model."""
    M = 2 * n - 1
    L_a = [[int(bool(model[alpha[k][i]])) for i in range(n)]
           for k in range(K)]
    L_b = [[int(bool(model[beta[k][i]])) for i in range(n)]
           for k in range(K)]
    g = [[int(bool(model[gamma[j][k]])) for k in range(K)]
         for j in range(M)]
    return L_a, L_b, g


def block_model(solver, alpha, beta, gamma, L_a, L_b, g, n, K):
    """Add a clause forbidding this exact assignment so the next
    check() returns a DIFFERENT model."""
    M = 2 * n - 1
    lits = []
    for k in range(K):
        for i in range(n):
            lits.append(alpha[k][i] if L_a[k][i] == 0 else Not(alpha[k][i]))
            lits.append(beta[k][i]  if L_b[k][i] == 0 else Not(beta[k][i]))
    for j in range(M):
        for k in range(K):
            lits.append(gamma[j][k] if g[j][k] == 0 else Not(gamma[j][k]))
    solver.add(Or(*lits))


def attempt(n, K, max_models=1, timeout_s=120):
    """Find up to max_models distinct SAT decompositions for polymul_n at K."""
    set_param("parallel.enable", True)
    solver, alpha, beta, gamma = encode_search(n, K)
    solver.set("timeout", timeout_s * 1000)
    found = []

    for idx in range(max_models):
        t0 = time.monotonic()
        result = solver.check()
        elapsed = time.monotonic() - t0
        if result != sat:
            verdict = "unsat" if result == unsat else "timeout"
            print(f"  n={n}, K={K}, model #{idx}: {verdict} ({elapsed:.1f}s)")
            return found, verdict

        model = solver.model()
        L_a, L_b, g = extract_model(model, alpha, beta, gamma, n, K)
        print(f"  n={n}, K={K}, model #{idx}: SAT ({elapsed:.1f}s)")
        found.append({
            "name": f"polymul_{n}_K{K}_idx{idx}",
            "n": n, "K": K,
            "L_a": L_a, "L_b": L_b, "gamma": g,
        })
        block_model(solver, alpha, beta, gamma, L_a, L_b, g, n, K)

    return found, "sat"


def build_library(targets, max_models=1, timeout_s=120):
    """Build the library.  `targets` is a list of (n, K)."""
    library = []
    for n, K in targets:
        print(f"\n--- polymul_{n}, K={K} ---")
        found, _ = attempt(n, K, max_models=max_models, timeout_s=timeout_s)
        library.extend(found)
    return library


def save(library, path=LIBRARY_PATH):
    """Save library to JSON."""
    with open(path, "w") as f:
        json.dump(library, f, indent=2)
    print(f"\n→ Saved {len(library)} entries to {path}")


def main():
    multi = 1
    if "--multi" in sys.argv:
        idx = sys.argv.index("--multi")
        multi = int(sys.argv[idx + 1])

    # Target list — span n=2..4 at and slightly above R(n).
    # Each runs with 2-min timeout.
    targets = [
        (2, 3),  # R(2) = 3 — Karatsuba
        (2, 4),  # naive 4-mult, super-optimal
        (3, 6),  # R(3) = 6
        (3, 7), (3, 8), (3, 9),  # super-optimal
        (4, 9),  # R(4) = 9
        (4, 10), (4, 11), (4, 12),  # super-optimal
    ]

    library = build_library(targets, max_models=multi, timeout_s=120)
    save(library)
    print(f"\nLibrary summary by (n, K):")
    seen = {}
    for e in library:
        key = (e["n"], e["K"])
        seen[key] = seen.get(key, 0) + 1
    for key in sorted(seen):
        print(f"  n={key[0]}, K={key[1]}: {seen[key]} model(s)")


if __name__ == "__main__":
    main()
