"""phase_d_enumerate.py — L1.2-pattern structural enumeration.

For K=7 ±1-coefficient 2×2 matmul decompositions:
  1. Enumerate distinct bilinear-form witnesses at threshold ≤ 36.
  2. For each, compute α/β/γ side SLP costs via slp_forms.
  3. Build a comprehensive table.

Strategy: SAT-block-iterate.  Each iteration finds a witness, then
adds a Hamming-distance blocker (or a literal-equality blocker)
ruling out THIS exact witness so the next solve finds a different
one.

Goal: produce the "structural impossibility narrative" — all K=7
±1 decompositions enumerated up to inherent symmetry, with their
SLP costs tabulated.  If all enumerated witnesses have total SLP
≥ 18, then 18 is the framework-checked minimum for ±1 K=7.
"""
import argparse
import sys
import time

from z3 import (And, Bool, BoolVal, If, Not, Or, Sum, sat, unsat,
                Solver, set_param)

sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/karstadt_schwartz_2x2')
from encoding import (
    make_vars, add_disjoint, add_tensor_constraints, add_nontrivial,
    add_sym_break, nonzero_count_expr, extract_model, verify_witness,
    count_nonzeros, print_witness,
    N_A, N_B, M,
)
from slp_forms import min_slp


K = 7


def witness_signature(alpha, beta, gamma):
    """Hashable summary of a witness for de-dup purposes."""
    return (tuple(tuple(row) for row in alpha),
            tuple(tuple(row) for row in beta),
            tuple(tuple(row) for row in gamma))


def block_witness(solver, a_p, a_n, b_p, b_n, g_p, g_n, alpha, beta, gamma, K):
    """Add a clause: NOT (current assignment of all pos/neg booleans).
    This rules out the exact witness; symmetric variants remain
    available."""
    lits = []
    for k in range(K):
        for i in range(N_A):
            ap_val = alpha[k][i] == 1
            an_val = alpha[k][i] == -1
            lits.append(a_p[k][i] if not ap_val else Not(a_p[k][i]))
            lits.append(a_n[k][i] if not an_val else Not(a_n[k][i]))
        for i in range(N_B):
            bp_val = beta[k][i] == 1
            bn_val = beta[k][i] == -1
            lits.append(b_p[k][i] if not bp_val else Not(b_p[k][i]))
            lits.append(b_n[k][i] if not bn_val else Not(b_n[k][i]))
    for j in range(M):
        for k in range(K):
            gp_val = gamma[j][k] == 1
            gn_val = gamma[j][k] == -1
            lits.append(g_p[j][k] if not gp_val else Not(g_p[j][k]))
            lits.append(g_n[j][k] if not gn_val else Not(g_n[j][k]))
    solver.add(Or(*lits))


def compute_slp_costs(alpha, beta, gamma, K, timeout_s=120):
    """Run min_slp on each of α, β, γ sides.  Returns (cost_a, cost_b, cost_g)
    or (None, None, None) if any side wedges."""
    # α: K linear forms over N_A inputs.
    alpha_forms = [tuple(row) for row in alpha]
    print(f"    Min-SLP α (K={K} forms, D={N_A}):", end=" ", flush=True)
    cost_a, _ = min_slp(alpha_forms, max_L=K, D=N_A, timeout_s=timeout_s,
                        verbose=False)
    print(f"{cost_a}")

    beta_forms = [tuple(row) for row in beta]
    print(f"    Min-SLP β (K={K} forms, D={N_B}):", end=" ", flush=True)
    cost_b, _ = min_slp(beta_forms, max_L=K, D=N_B, timeout_s=timeout_s,
                        verbose=False)
    print(f"{cost_b}")

    gamma_forms = [tuple(row) for row in gamma]
    print(f"    Min-SLP γ (M={M} forms, D={K}):", end=" ", flush=True)
    cost_g, _ = min_slp(gamma_forms, max_L=M*K, D=K, timeout_s=timeout_s,
                        verbose=False)
    print(f"{cost_g}")
    return cost_a, cost_b, cost_g


def enumerate_witnesses(max_witnesses=10, threshold=36, search_timeout=600,
                        slp_timeout=120):
    """Enumerate distinct K=7 ±1 bilinear witnesses at Σ|nz| ≤ threshold.
    For each, compute SLP costs.  Tabulate."""
    set_param("parallel.enable", True)

    print(f"Phase D enumeration: K={K} ±1 bilinear decomps at Σ|nz| ≤ {threshold}.")
    print(f"  Max witnesses: {max_witnesses}.")
    print(f"  Per-search timeout: {search_timeout}s.")
    print(f"  Per-SLP timeout: {slp_timeout}s.\n")

    # Build initial solver with sym break.
    solver = Solver()
    a_p, a_n, b_p, b_n, g_p, g_n = make_vars(K)
    add_disjoint(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)
    add_tensor_constraints(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)
    add_nontrivial(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)
    add_sym_break(solver, a_p, a_n, b_p, b_n, g_p, g_n, K)
    nz_expr = nonzero_count_expr(a_p, a_n, b_p, b_n, g_p, g_n, K)
    solver.add(nz_expr <= threshold)
    solver.set("timeout", search_timeout * 1000)

    witnesses = []
    table = []
    iter_num = 0
    while len(witnesses) < max_witnesses:
        iter_num += 1
        print(f"--- Iteration {iter_num} ---")
        t0 = time.monotonic()
        r = solver.check()
        elapsed = time.monotonic() - t0
        print(f"  Z3: {r}  ({elapsed:.2f}s)")
        sys.stdout.flush()
        if r == unsat:
            print(f"  *** UNSAT after {iter_num-1} witnesses: enumeration "
                  f"exhausted. ***")
            break
        if r != sat:
            print(f"  *** TIMEOUT/UNKNOWN at iteration {iter_num} — "
                  f"halting. ***")
            break
        m = solver.model()
        alpha, beta, gamma = extract_model(m, a_p, a_n, b_p, b_n, g_p, g_n, K)
        ok, fail = verify_witness(alpha, beta, gamma, K)
        if not ok:
            print(f"  VERIFY-FAIL: {fail}")
            break
        sig = witness_signature(alpha, beta, gamma)
        nz = count_nonzeros(alpha, beta, gamma)
        print(f"  Witness #{iter_num}: Σ|nz|={nz}")
        print_witness(alpha, beta, gamma, K, label=f"W#{iter_num}")

        # Compute SLP costs.
        cost_a, cost_b, cost_g = compute_slp_costs(alpha, beta, gamma, K,
                                                    timeout_s=slp_timeout)
        total = (cost_a or 0) + (cost_b or 0) + (cost_g or 0) \
                if all(c is not None for c in (cost_a, cost_b, cost_g)) \
                else None
        print(f"    Total SLP cost: {total}")

        witnesses.append({
            "iter": iter_num,
            "sig": sig,
            "alpha": alpha, "beta": beta, "gamma": gamma,
            "nz": nz, "slp_a": cost_a, "slp_b": cost_b, "slp_g": cost_g,
            "slp_total": total,
            "elapsed": elapsed,
        })
        table.append({
            "iter": iter_num, "nz": nz,
            "slp_a": cost_a, "slp_b": cost_b, "slp_g": cost_g,
            "slp_total": total,
        })

        # Block this witness.
        block_witness(solver, a_p, a_n, b_p, b_n, g_p, g_n,
                      alpha, beta, gamma, K)

    print(f"\n{'='*60}")
    print(f"Summary: {len(witnesses)} witnesses enumerated.")
    print(f"{'='*60}")
    print(f"{'#':<3} {'Σ|nz|':>5} {'SLP_α':>5} {'SLP_β':>5} {'SLP_γ':>5} "
          f"{'Total':>5}")
    print("-" * 35)
    for row in table:
        total_s = str(row["slp_total"]) if row["slp_total"] is not None else "—"
        print(f"{row['iter']:<3} {row['nz']:>5} "
              f"{str(row['slp_a']):>5} {str(row['slp_b']):>5} "
              f"{str(row['slp_g']):>5} {total_s:>5}")

    if witnesses:
        valid_totals = [w["slp_total"] for w in witnesses
                        if w["slp_total"] is not None]
        if valid_totals:
            min_total = min(valid_totals)
            print(f"\nMin total SLP cost across enumerated witnesses: {min_total}")
    return witnesses


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--max", type=int, default=8,
                   help="Max witnesses to enumerate")
    p.add_argument("--threshold", type=int, default=36,
                   help="Σ|nz| ≤ threshold")
    p.add_argument("--search-timeout", type=int, default=600)
    p.add_argument("--slp-timeout", type=int, default=120)
    args = p.parse_args()

    enumerate_witnesses(max_witnesses=args.max,
                        threshold=args.threshold,
                        search_timeout=args.search_timeout,
                        slp_timeout=args.slp_timeout)
    return 0


if __name__ == "__main__":
    sys.exit(main())
