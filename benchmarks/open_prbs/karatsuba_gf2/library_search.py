"""library_search.py — Part A+B: search polymul_N using
library entries as fixed sub-blocks.

Each library entry is a CONCRETE bilinear decomposition of
polymul_n at some rank K.  When we use it in a larger polymul_N
search, we apply it to (L·a, L'·b) where L, L' are search-
variable matrices mapping polymul_N's inputs into the library
entry's input space.

Compared to hybrid_search (which used UF axioms over symbolic
polymul_k), library-aware search EXPANDS the polymul_n
decomposition at encoding time — Z3 sees specific bilinear
forms, not abstract UF calls.

Part B extension: a SPECULATIVE entry s ∈ S has unknown
(L_a, L_b, γ) — variables in the search.  If the search SATs,
we have a polymul_N decomposition CONDITIONAL on s satisfying
polymul_n's tensor at those variables.  The DISCHARGE step
verifies s by a small dedicated search.

Usage:
    python library_search.py N [--use n1,K1 n2,K2 ...] [--K K] [--timeout T]
       --use NL,KL    Each lib_entry by (n, K) tag from library.json.
       --speculate n,K   Add a speculative entry (unverified) at (n, K).
       --K K          Target total cost (defaults to sum of K over uses).
       --timeout T    Z3 timeout in seconds.

Examples:
    python library_search.py 5 --use 3,6 3,6 --K 13
       Solve polymul_5 = 2 × (polymul_3 K=6) + extra fitting K_total=13.

    python library_search.py 5 --use 3,6 --speculate 3,6
       Solve polymul_5 = polymul_3-known + polymul_3-speculated.
"""
from z3 import (And, Bool, BoolVal, Not, Or, Solver, Xor,
                sat, unsat, set_param)
import json
import sys
import time
from pathlib import Path


HERE = Path(__file__).parent
LIBRARY_PATH = HERE / "library.json"


def load_library():
    with open(LIBRARY_PATH) as f:
        return json.load(f)


def lookup_entry(library, n, K, idx=0):
    """Find the idx-th library entry with given (n, K)."""
    matches = [e for e in library if e["n"] == n and e["K"] == K]
    if not matches:
        return None
    return matches[idx % len(matches)]


def target_tensor(n):
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


def encode_with_library(N, uses, speculates, timeout_s=600):
    """Search for polymul_N decomposition using library entries.

    uses: list of dicts (n, K, L_a, L_b, gamma) — TRUSTED entries.
    speculates: list of (n, K) tuples — UNVERIFIED entries (L_a, L_b, γ unknown).
    """
    set_param("parallel.enable", True)
    solver = Solver()
    solver.set("timeout", timeout_s * 1000)
    M_N = 2 * N - 1

    # For each USED entry, allocate L^use (size n × N) and L'^use
    # (size n × N) — how the entry's inputs are mapped from polymul_N's inputs.
    used_block_info = []
    for use_idx, e in enumerate(uses):
        n_e = e["n"]
        K_e = e["K"]
        # L^use[i][j]: entry's input i is XOR over j-th polymul_N inputs.
        L_use_a = [[Bool(f"useL_a_{use_idx}_{i}_{j}")
                    for j in range(N)] for i in range(n_e)]
        L_use_b = [[Bool(f"useL_b_{use_idx}_{i}_{j}")
                    for j in range(N)] for i in range(n_e)]
        used_block_info.append({
            "entry": e,
            "L_use_a": L_use_a,
            "L_use_b": L_use_b,
            "k_offset": None,  # set below; index into the flat list of bilinear products.
        })

    # For each SPECULATIVE entry, allocate the entry's (α, β, γ) as
    # search variables AND L^spec (n × N), L'^spec (n × N) for the
    # outer mapping.  Constraint: the speculative entry's (α, β, γ)
    # must satisfy polymul_n's tensor.
    spec_block_info = []
    for spec_idx, (n_s, K_s) in enumerate(speculates):
        # The spec entry's INTERNAL (L_a, L_b, γ) — fully variable.
        spec_L_a = [[Bool(f"specA_{spec_idx}_{k}_{i}")
                     for i in range(n_s)] for k in range(K_s)]
        spec_L_b = [[Bool(f"specB_{spec_idx}_{k}_{i}")
                     for i in range(n_s)] for k in range(K_s)]
        spec_gamma = [[Bool(f"specG_{spec_idx}_{j}_{k}")
                       for k in range(K_s)] for j in range(2*n_s - 1)]
        # Outer mapping into the speculative entry's input space.
        L_use_a = [[Bool(f"specL_a_{spec_idx}_{i}_{j}")
                    for j in range(N)] for i in range(n_s)]
        L_use_b = [[Bool(f"specL_b_{spec_idx}_{i}_{j}")
                    for j in range(N)] for i in range(n_s)]
        # Constraint: spec's internal (L_a, L_b, γ) satisfies polymul_n's tensor.
        T_n = target_tensor(n_s)
        for j in range(2*n_s - 1):
            for i in range(n_s):
                for ii in range(n_s):
                    terms = [And(spec_gamma[j][k], spec_L_a[k][i], spec_L_b[k][ii])
                             for k in range(K_s)]
                    xor = xor_all(terms)
                    if T_n[j][i][ii] == 1:
                        solver.add(xor)
                    else:
                        solver.add(Not(xor))
        # Non-trivial mults / used.
        for k in range(K_s):
            solver.add(Or(*spec_L_a[k]))
            solver.add(Or(*spec_L_b[k]))
        spec_block_info.append({
            "n": n_s, "K": K_s,
            "spec_L_a": spec_L_a, "spec_L_b": spec_L_b,
            "spec_gamma": spec_gamma,
            "L_use_a": L_use_a, "L_use_b": L_use_b,
        })

    # Compute the EFFECTIVE bilinear products from each block.
    # Each block contributes K_block × M_block "values" (each K_block
    # is a bilinear product evaluated over polymul_N's inputs, after
    # composing through the block's internal (L_a, L_b, γ)).
    #
    # For a USED entry with (L^use, L'^use, fixed L_a^lib, L_b^lib, γ^lib):
    #   Block-output[j_lib] is a bilinear form in polymul_N's (a, b).
    #   Specifically:
    #     block_output[j_lib] = ⊕_k γ^lib[j_lib][k] · α_k(a) · β_k(b)
    #   where α_k(a) = ⊕_i L_a^lib[k][i] · (⊕_p L^use[i][p] · a_p)
    #               = ⊕_p (⊕_i L_a^lib[k][i] · L^use[i][p]) · a_p
    #     similarly β_k(b).
    #
    # For a SPEC entry, same but with spec_L_a, spec_L_b instead of fixed.
    #
    # Then for polymul_N output j ∈ [0, M_N):
    #   polymul_N output j = ⊕_block ⊕_j_lib γ^outer[j][block][j_lib] · block_output[j_lib]
    #
    # The polymul_N output j as a bilinear form in (a, b):
    #   polymul_N[j] = ⊕_blocks ⊕_j_lib γ^outer · ⊕_k γ^block[j_lib][k] ·
    #                  α_k(L^use · a) · β_k(L'^use · b)
    #   = ⊕_(b, j_lib, k) γ^outer[j][b][j_lib] · γ^block[j_lib][k] · α_k(L^use · a) · β_k(L'^use · b)
    #
    # We want this to equal T_N[j][i][i'] when expanded as ⊕ a_i b_i'.

    # Build a flat list of (block, j_lib, k) tuples — each is a
    # bilinear product slot, with its α and β coefficient vectors
    # expressed over polymul_N's input space.
    flat_slots = []  # each: {alpha_N: list[N booleans expr], beta_N: list[N booleans expr]}
    for ublock in used_block_info:
        e = ublock["entry"]
        n_e = e["n"]
        K_e = e["K"]
        M_e = 2 * n_e - 1
        L_use_a = ublock["L_use_a"]
        L_use_b = ublock["L_use_b"]
        L_a_lib = e["L_a"]
        L_b_lib = e["L_b"]
        gamma_lib = e["gamma"]
        # For each j_lib in [0, M_e), the block's j_lib-th output is
        #   ⊕_k γ_lib[j_lib][k] · α_k(L^use · a) · β_k(L'^use · b).
        # We represent this output as a sum of (α_k, β_k) bilinear forms,
        # gated by γ_lib (which is fixed 0/1 from the library entry).
        for j_lib in range(M_e):
            for k in range(K_e):
                if gamma_lib[j_lib][k] != 1:
                    continue
                # This (k, j_lib) is selected by γ_lib.
                # α_k(L^use · a) = ⊕_i L_a_lib[k][i] AND L^use[i] = vector
                # over N booleans: ⊕_i L_a_lib[k][i] · L^use[i][p] for each p.
                alpha_N = []
                for p in range(N):
                    # ⊕_i L_a_lib[k][i] AND L_use_a[i][p].  L_a_lib[k][i] is 0/1 constant.
                    terms = []
                    for i in range(n_e):
                        if L_a_lib[k][i] == 1:
                            terms.append(L_use_a[i][p])
                    alpha_N.append(xor_all(terms))
                beta_N = []
                for p in range(N):
                    terms = []
                    for i in range(n_e):
                        if L_b_lib[k][i] == 1:
                            terms.append(L_use_b[i][p])
                    beta_N.append(xor_all(terms))
                flat_slots.append({
                    "alpha_N": alpha_N,
                    "beta_N": beta_N,
                    "block_j_lib": (id(ublock), j_lib, k),
                })
    for sblock in spec_block_info:
        n_s = sblock["n"]
        K_s = sblock["K"]
        M_s = 2 * n_s - 1
        L_use_a = sblock["L_use_a"]
        L_use_b = sblock["L_use_b"]
        spec_L_a = sblock["spec_L_a"]
        spec_L_b = sblock["spec_L_b"]
        spec_gamma = sblock["spec_gamma"]
        # For SPEC, the gamma is a search variable.  The block-output
        # is a conditional XOR sum.
        for j_lib in range(M_s):
            for k in range(K_s):
                # α_k effective on N inputs:
                alpha_N = []
                for p in range(N):
                    # ⊕_i spec_L_a[k][i] AND L_use_a[i][p]
                    terms = [And(spec_L_a[k][i], L_use_a[i][p]) for i in range(n_s)]
                    alpha_N.append(xor_all(terms))
                beta_N = []
                for p in range(N):
                    terms = [And(spec_L_b[k][i], L_use_b[i][p]) for i in range(n_s)]
                    beta_N.append(xor_all(terms))
                # Gate this slot by spec_gamma[j_lib][k].  We'll use an
                # AND-gated slot — flatten by AND-ing with the gate.
                flat_slots.append({
                    "alpha_N": alpha_N,
                    "beta_N": beta_N,
                    "gate": spec_gamma[j_lib][k],
                    "block_j_lib": (id(sblock), j_lib, k),
                })

    # Outer γ: gamma^outer[j][slot] for j in [0, M_N), slot in flat_slots.
    n_slots = len(flat_slots)
    gamma_outer = [[Bool(f"gO_{j}_{s}") for s in range(n_slots)]
                   for j in range(M_N)]

    # Tensor equality: for each (j, i, i'):
    #   ⊕_slot γ_outer[j][slot] · gate(slot) · alpha_N[slot][i] · beta_N[slot][i'] ≡ T[j][i][i'].
    T_N = target_tensor(N)
    for j in range(M_N):
        for i in range(N):
            for ii in range(N):
                # For each slot, the contribution to a_i·b_i' is:
                # γ_outer[j][slot] · (gate(slot) if SPEC else 1) · alpha_N[slot][i] · beta_N[slot][ii].
                terms = []
                for s, slot in enumerate(flat_slots):
                    gate = slot.get("gate")
                    if gate is None:
                        # Used entry (fixed slot — always contributes if γ_outer chooses).
                        terms.append(And(gamma_outer[j][s],
                                         slot["alpha_N"][i],
                                         slot["beta_N"][ii]))
                    else:
                        terms.append(And(gamma_outer[j][s], gate,
                                         slot["alpha_N"][i],
                                         slot["beta_N"][ii]))
                xor = xor_all(terms)
                if T_N[j][i][ii] == 1:
                    solver.add(xor)
                else:
                    solver.add(Not(xor))

    return solver, used_block_info, spec_block_info, gamma_outer, flat_slots


def cost_of_uses_speculates(uses, speculates):
    """Estimate cost: sum of K over uses + sum of K over speculates."""
    return sum(e["K"] for e in uses) + sum(K for _, K in speculates)


def search(N, uses, speculates, timeout_s=600):
    print(f"Library-aware search for polymul_{N}:")
    cost = cost_of_uses_speculates(uses, speculates)
    print(f"  uses: {[(e['n'], e['K']) for e in uses]}")
    print(f"  speculates: {speculates}")
    print(f"  TOTAL COST: {cost} scalar mults (vs ~13 published for n=5).")
    print(f"  timeout: {timeout_s}s")

    solver, used_info, spec_info, gamma_outer, flat_slots = encode_with_library(
        N, uses, speculates, timeout_s=timeout_s)
    n_slots = len(flat_slots)
    n_constraints = (2*N - 1) * N * N
    # Count search variables (rough).
    n_outer = (2*N - 1) * n_slots
    n_outer_L = sum(N * e["n"] * 2 for e in uses) + sum(N * n * 2 for n, _ in speculates)
    n_inner_spec = sum(K * n * 2 + (2*n - 1) * K for n, K in speculates)
    n_total = n_outer + n_outer_L + n_inner_spec
    print(f"  Search variables (rough): {n_total} "
          f"({n_outer} γ_outer + {n_outer_L} L_use + {n_inner_spec} inner-spec)")
    print(f"  Tensor constraints: {n_constraints}")

    t0 = time.monotonic()
    result = solver.check()
    elapsed = time.monotonic() - t0
    print(f"\n  Z3 result: {result}  ({elapsed:.1f}s)")

    if result == sat:
        model = solver.model()
        print(f"\n*** SAT: polymul_{N} decomposition found (cost {cost}). ***")
        if cost < 13 and N == 5:
            print(f"    BEATS published R(5) ≤ 13.")
        # Print outer γ-combiner for each output.
        for j in range(2*N - 1):
            selected = [s for s in range(n_slots) if bool(model[gamma_outer[j][s]])]
            print(f"  out[{j}] = ⊕ slots {selected}")
        return 0
    elif result == unsat:
        print(f"\n*** UNSAT: this configuration cannot decompose polymul_{N}. ***")
        return 0
    else:
        print(f"\n*** TIMEOUT. ***")
        return 1


def parse_args(argv):
    N = int(argv[1])
    uses_spec = []
    speculates = []
    timeout = 600
    i = 2
    while i < len(argv):
        if argv[i] == "--use":
            i += 1
            while i < len(argv) and not argv[i].startswith("--"):
                n_K = argv[i].split(",")
                uses_spec.append((int(n_K[0]), int(n_K[1])))
                i += 1
        elif argv[i] == "--speculate":
            i += 1
            while i < len(argv) and not argv[i].startswith("--"):
                n_K = argv[i].split(",")
                speculates.append((int(n_K[0]), int(n_K[1])))
                i += 1
        elif argv[i] == "--timeout":
            timeout = int(argv[i+1])
            i += 2
        else:
            i += 1
    return N, uses_spec, speculates, timeout


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 1
    N, uses_spec, speculates, timeout = parse_args(sys.argv)
    library = load_library()
    uses = []
    for n, K in uses_spec:
        e = lookup_entry(library, n, K, idx=len(uses))  # cycle through if multiple specified
        if e is None:
            print(f"WARNING: no library entry for (n={n}, K={K}); skipping.")
            continue
        uses.append(e)
    return search(N, uses, speculates, timeout_s=timeout)


if __name__ == "__main__":
    sys.exit(main())
