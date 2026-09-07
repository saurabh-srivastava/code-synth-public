"""sweep_speculations.py — scan structural classes for L1.2 K=10.

For each speculation, runs the search and reports the verdict.
The framework: choose a verified library entry + a sub-block
mapping (which A/B indices it operates on) + K_extra parametric
rank-1 supplements.  Search for γ combiners.

Total mults: K_lib + K_extra.  Targeting K=10 (= Hopcroft-Kerr -1).

Each structural class is a (library_entry_name, a_mapping,
b_mapping, K_extra) tuple.  The 2×3 × 3×2 problem has multiple
ways to pick a 2×2 sub-block (3 col-pair choices × 3 row-pair
choices) — by symmetry the col×row mappings that index the
SAME k-position align (col k_a of A with row k_b of B for
the inner sum, k_a == k_b).
"""
from z3 import (And, Bool, BoolVal, If, Not, Or, Solver, Sum,
                Xor, sat, unsat, set_param)
import sys
import time

sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/hopcroft_kerr_2x3x2')
from library import LIBRARY


N_A = 6  # 2x3 = 6
N_B = 6  # 3x2 = 6
M   = 4  # 2x2 = 4


def target_tensor():
    T = [[[0] * N_B for _ in range(N_A)] for _ in range(M)]
    for i in range(2):
        for j in range(2):
            c_idx = i * 2 + j
            for k in range(3):
                a_idx = i * 3 + k
                b_idx = k * 2 + j
                T[c_idx][a_idx][b_idx] = 1
    return T


def a_mapping_for_cols(cols):
    """Given cols ⊆ {0,1,2}, return A indices for those columns
    (in row-major: a00, a01, a02, a10, a11, a12)."""
    out = []
    for row in [0, 1]:
        for col in cols:
            out.append(row * 3 + col)
    return out


def b_mapping_for_rows(rows):
    """Given rows ⊆ {0,1,2}, return B indices for those rows."""
    out = []
    for row in rows:
        for col in [0, 1]:
            out.append(row * 2 + col)
    return out


def effective_bilinear_forms(library_entry, a_mapping, b_mapping):
    """Map library entry's bilinear forms onto the global 6-dim A
    and 6-dim B input space using a_mapping and b_mapping."""
    K = library_entry["K"]
    s_La = []
    s_Lb = []
    for k in range(K):
        la = [0] * N_A
        lb = [0] * N_B
        for local_i, global_i in enumerate(a_mapping):
            la[global_i] = library_entry["L_a"][k][local_i]
        for local_i, global_i in enumerate(b_mapping):
            lb[global_i] = library_entry["L_b"][k][local_i]
        s_La.append(la)
        s_Lb.append(lb)
    return s_La, s_Lb


def encode_search(library_instances, K_extra, sym_break=True):
    """library_instances: list of (entry_name, a_mapping, b_mapping)."""
    solver = Solver()

    # For each library instance, expand its bilinear forms.
    fixed_blocks = []  # list of (La_global, Lb_global) per library instance
    K_fixed = 0
    for name, a_map, b_map in library_instances:
        entry = LIBRARY[name]
        s_La, s_Lb = effective_bilinear_forms(entry, a_map, b_map)
        fixed_blocks.append((s_La, s_Lb))
        K_fixed += entry["K"]

    K_total = K_fixed + K_extra

    # Extra mults: parametric ±1.
    e_a_p = [[Bool(f"ea_p_{k}_{i}") for i in range(N_A)] for k in range(K_extra)]
    e_a_n = [[Bool(f"ea_n_{k}_{i}") for i in range(N_A)] for k in range(K_extra)]
    e_b_p = [[Bool(f"eb_p_{k}_{i}") for i in range(N_B)] for k in range(K_extra)]
    e_b_n = [[Bool(f"eb_n_{k}_{i}") for i in range(N_B)] for k in range(K_extra)]
    for k in range(K_extra):
        for i in range(N_A):
            solver.add(Not(And(e_a_p[k][i], e_a_n[k][i])))
        for i in range(N_B):
            solver.add(Not(And(e_b_p[k][i], e_b_n[k][i])))

    # γ over all K_total mults.
    g_p = [[Bool(f"gp_{j}_{k}") for k in range(K_total)] for j in range(M)]
    g_n = [[Bool(f"gn_{j}_{k}") for k in range(K_total)] for j in range(M)]
    for j in range(M):
        for k in range(K_total):
            solver.add(Not(And(g_p[j][k], g_n[j][k])))

    T = target_tensor()
    for j in range(M):
        for ia in range(N_A):
            for ib in range(N_B):
                terms = []
                offset = 0
                for (s_La, s_Lb), instance in zip(fixed_blocks, library_instances):
                    entry = LIBRARY[instance[0]]
                    K_inst = entry["K"]
                    for k in range(K_inst):
                        coeff_const = s_La[k][ia] * s_Lb[k][ib]
                        if coeff_const == 0:
                            continue
                        g_val = If(g_p[j][offset + k], 1, 0) - If(g_n[j][offset + k], 1, 0)
                        terms.append(coeff_const * g_val)
                    offset += K_inst
                for k_ext in range(K_extra):
                    k = K_fixed + k_ext
                    # Flat boolean encoding to avoid NIA wedge.
                    nz = And(Or(g_p[j][k], g_n[j][k]),
                             Or(e_a_p[k_ext][ia], e_a_n[k_ext][ia]),
                             Or(e_b_p[k_ext][ib], e_b_n[k_ext][ib]))
                    neg = Xor(g_n[j][k],
                              Xor(e_a_n[k_ext][ia], e_b_n[k_ext][ib]))
                    terms.append(If(nz, If(neg, -1, 1), 0))
                if terms:
                    solver.add(Sum(terms) == T[j][ia][ib])
                else:
                    solver.add(T[j][ia][ib] == 0)

    # Non-trivial extras.
    for k in range(K_extra):
        solver.add(Or(*[Or(e_a_p[k][i], e_a_n[k][i]) for i in range(N_A)]))
        solver.add(Or(*[Or(e_b_p[k][i], e_b_n[k][i]) for i in range(N_B)]))
        solver.add(Or(*[Or(g_p[j][K_fixed + k], g_n[j][K_fixed + k])
                        for j in range(M)]))

    if sym_break and K_extra > 1:
        def sig(k):
            s = []
            for i in range(N_A):
                s += [e_a_p[k][i], e_a_n[k][i]]
            for i in range(N_B):
                s += [e_b_p[k][i], e_b_n[k][i]]
            for j in range(M):
                s += [g_p[j][K_fixed + k], g_n[j][K_fixed + k]]
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

    return solver, K_fixed, K_total


def run_speculation(name, library_instances, K_extra, timeout_s=600):
    set_param("parallel.enable", True)
    solver, K_fixed, K_total = encode_search(library_instances, K_extra)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    result = solver.check()
    elapsed = time.monotonic() - t0

    inst_strs = [f"{n}({a_map}×{b_map})"
                 for n, a_map, b_map in library_instances]
    print(f"\n[{name}] K_fixed={K_fixed} ({', '.join(inst_strs)}) "
          f"+ K_extra={K_extra} → K_total={K_total}")
    print(f"  Z3: {result}  ({elapsed:.2f}s)")
    sys.stdout.flush()
    return str(result), elapsed


def main():
    print("Sweep of structural speculations for 2×3 × 3×2 over ℤ:")
    print(f"Target: K=10 (would beat Hopcroft-Kerr 11).")

    results = []

    # S1: Strassen on cols/rows (0,1) + 3 extras.
    a01 = a_mapping_for_cols([0, 1])
    b01 = b_mapping_for_rows([0, 1])
    results.append(("S1: Strassen(k=0,1) + 3",
                    run_speculation("S1", [("strassen_2x2", a01, b01)], 3)))

    # S2: Strassen on cols/rows (1,2) + 3 extras.
    a12 = a_mapping_for_cols([1, 2])
    b12 = b_mapping_for_rows([1, 2])
    results.append(("S2: Strassen(k=1,2) + 3",
                    run_speculation("S2", [("strassen_2x2", a12, b12)], 3)))

    # S3: Strassen on cols/rows (0,2) + 3 extras.
    a02 = a_mapping_for_cols([0, 2])
    b02 = b_mapping_for_rows([0, 2])
    results.append(("S3: Strassen(k=0,2) + 3",
                    run_speculation("S3", [("strassen_2x2", a02, b02)], 3)))

    # S4: Naive 2×2 (K=8) on (0,1) + 2 extras = K=10.
    results.append(("S4: Naive 2x2(k=0,1) + 2",
                    run_speculation("S4", [("naive_2x2", a01, b01)], 2)))

    # S5: Outer product (K=4) on (col 2, row 2) + 6 extras = K=10.
    # 2x1 col is a02, a12 (cols of A); 1x2 row is b20, b21.
    out_a = [2, 5]      # a02, a12
    out_b = [4, 5]      # b20, b21
    results.append(("S5: Outer(col 2) + 6",
                    run_speculation("S5", [("outer_2x1_1x2", out_a, out_b)], 6)))

    # S6: Two outer products + 2 extras = 8 + 2 = 10.
    # Outer on (col 0, row 0): A col 0 = (a00, a10) = [0, 3]; B row 0 = (b00, b01) = [0, 1].
    out_a0 = [0, 3]
    out_b0 = [0, 1]
    # Outer on (col 2, row 2): a02, a12 = [2, 5]; b20, b21 = [4, 5].
    out_a2 = [2, 5]
    out_b2 = [4, 5]
    results.append(("S6: 2×Outer(k=0,2) + 2",
                    run_speculation(
                        "S6",
                        [("outer_2x1_1x2", out_a0, out_b0),
                         ("outer_2x1_1x2", out_a2, out_b2)], 2)))

    # S7: Strassen + 4 extras = 11 baseline (sanity SAT check).
    results.append(("S7: Strassen(k=0,1) + 4 (baseline K=11)",
                    run_speculation("S7", [("strassen_2x2", a01, b01)], 4)))

    # Summary table.
    print("\n" + "=" * 60)
    print(f"{'Speculation':<40} {'Verdict':<10} {'Time':>10}")
    print("=" * 60)
    for name, (verdict, t) in results:
        print(f"{name:<40} {verdict:<10} {t:>8.2f}s")


if __name__ == "__main__":
    main()
