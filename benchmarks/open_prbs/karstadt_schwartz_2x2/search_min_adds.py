"""search_min_adds.py — search for K=7 bilinear decompositions minimizing
total nonzero coefficients (≡ minimizing additions) for 2×2 matmul.

Two modes:
  - sweep:   ascending check at each Σ|nz| threshold ∈ [floor, ceiling].
             First SAT is the minimum.  UNSAT below the SAT confirms
             a Z3-kernel-checked lower bound.
  - optimize: Z3 Optimize() with soft constraints — let Z3 find min directly.

Usage:
  python search_min_adds.py sweep   [--floor 30] [--ceiling 36] [--timeout 600]
  python search_min_adds.py optimize [--timeout 1800]
  python search_min_adds.py at K --threshold 33   # single-threshold SAT
"""
import argparse
import sys
import time
from z3 import (Solver, Optimize, set_param, sat, unsat, unknown, Sum, If,
                Or, Not)

sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/karstadt_schwartz_2x2')
from encoding import (
    make_vars, add_disjoint, add_tensor_constraints, add_nontrivial,
    add_sym_break, nonzero_count_expr, additions_from_nonzeros,
    extract_model, verify_witness, count_nonzeros, print_witness,
    N_A, N_B, M,
)

K = 7  # fixed bilinear rank


def build_base_solver(use_optimize=False, sym_break=True):
    """Build the base set of constraints; return solver + all vars."""
    s = Optimize() if use_optimize else Solver()
    a_p, a_n, b_p, b_n, g_p, g_n = make_vars(K)
    add_disjoint(s, a_p, a_n, b_p, b_n, g_p, g_n, K)
    add_tensor_constraints(s, a_p, a_n, b_p, b_n, g_p, g_n, K)
    add_nontrivial(s, a_p, a_n, b_p, b_n, g_p, g_n, K)
    if sym_break:
        add_sym_break(s, a_p, a_n, b_p, b_n, g_p, g_n, K)
    return s, a_p, a_n, b_p, b_n, g_p, g_n


def check_at_threshold(threshold, timeout_s=600):
    """Check SAT at Σ|nz| ≤ threshold.  Returns (verdict, elapsed, witness_or_None)."""
    set_param("parallel.enable", True)
    s, a_p, a_n, b_p, b_n, g_p, g_n = build_base_solver()
    nz_expr = nonzero_count_expr(a_p, a_n, b_p, b_n, g_p, g_n, K)
    s.add(nz_expr <= threshold)
    s.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    r = s.check()
    elapsed = time.monotonic() - t0
    if r == sat:
        m = s.model()
        alpha, beta, gamma = extract_model(m, a_p, a_n, b_p, b_n, g_p, g_n, K)
        return "sat", elapsed, (alpha, beta, gamma)
    elif r == unsat:
        return "unsat", elapsed, None
    else:
        return "timeout", elapsed, None


def cmd_sweep(args):
    """Sweep Σ|nz| ascending from floor until SAT, then UNSAT until floor.
    Reports the minimum SAT (= optimum) and confirms UNSAT below it."""
    print(f"Sweep Σ|nz| ∈ [{args.floor}, {args.ceiling}] for K={K} 2×2 matmul.")
    print(f"  Additions = Σ|nz| - {2*K + M}")
    print(f"  Per-threshold timeout: {args.timeout}s")
    print()
    print(f"  {'threshold':>10}  {'additions':>10}  {'verdict':<8}  {'time':>8}")
    print(f"  {'-'*10}  {'-'*10}  {'-'*8}  {'-'*8}")

    results = []
    best_sat = None
    best_witness = None
    # Ascending search: find smallest SAT.
    for thr in range(args.floor, args.ceiling + 1):
        adds = thr - (2*K + M)
        verdict, elapsed, witness = check_at_threshold(thr, args.timeout)
        results.append((thr, adds, verdict, elapsed))
        print(f"  {thr:>10}  {adds:>10}  {verdict:<8}  {elapsed:>7.2f}s")
        sys.stdout.flush()
        if verdict == "sat":
            best_sat = thr
            best_witness = witness
            break
        elif verdict == "timeout":
            print(f"  TIMEOUT at threshold {thr}; aborting sweep.")
            break

    if best_sat is None:
        print(f"\nNo SAT found in [{args.floor}, {args.ceiling}].")
        return 1

    print(f"\nFirst SAT at Σ|nz| = {best_sat} ({best_sat - (2*K+M)} additions).")
    alpha, beta, gamma = best_witness
    ok, fail = verify_witness(alpha, beta, gamma, K)
    if not ok:
        print(f"  CROSS-CHECK FAILED: {fail}")
        return 1
    print_witness(alpha, beta, gamma, K,
                  label=f"Z3 witness at Σ|nz| = {best_sat}")

    # Descending confirmation: UNSAT below best_sat down to floor.
    print(f"\nConfirm UNSAT for thresholds < {best_sat}:")
    print(f"  {'threshold':>10}  {'additions':>10}  {'verdict':<8}  {'time':>8}")
    print(f"  {'-'*10}  {'-'*10}  {'-'*8}  {'-'*8}")
    for thr in range(best_sat - 1, args.floor - 1, -1):
        adds = thr - (2*K + M)
        verdict, elapsed, _ = check_at_threshold(thr, args.timeout)
        results.append((thr, adds, verdict, elapsed))
        print(f"  {thr:>10}  {adds:>10}  {verdict:<8}  {elapsed:>7.2f}s")
        sys.stdout.flush()
        if verdict == "sat":
            print(f"  *** UNEXPECTED SAT at {thr} — investigate ***")
            return 1
        if verdict == "timeout":
            print(f"  TIMEOUT at threshold {thr}.")
            break

    print(f"\nResult: minimum Σ|nz| = {best_sat}, additions = {best_sat - (2*K+M)}.")
    return 0


def cmd_at(args):
    """Single-threshold SAT check."""
    print(f"K={K}, threshold Σ|nz| ≤ {args.threshold}, timeout {args.timeout}s.")
    verdict, elapsed, witness = check_at_threshold(args.threshold, args.timeout)
    print(f"\n  Z3: {verdict}  ({elapsed:.2f}s)")
    if verdict == "sat":
        alpha, beta, gamma = witness
        ok, fail = verify_witness(alpha, beta, gamma, K)
        if not ok:
            print(f"  CROSS-CHECK FAILED: {fail}")
            return 1
        print_witness(alpha, beta, gamma, K,
                      label=f"witness at Σ|nz| ≤ {args.threshold}")
        return 0
    elif verdict == "unsat":
        adds = args.threshold - (2*K + M)
        print(f"  *** Σ|nz| ≤ {args.threshold} ({adds} adds) is UNSAT for "
              f"K={K} 2×2 matmul. ***")
        return 0
    else:
        return 1


def cmd_optimize(args):
    """Use Z3 Optimize to find minimum directly."""
    set_param("parallel.enable", True)
    print(f"Z3 Optimize for min Σ|nz| at K={K}.  Timeout {args.timeout}s.")
    o, a_p, a_n, b_p, b_n, g_p, g_n = build_base_solver(use_optimize=True)
    nz_expr = nonzero_count_expr(a_p, a_n, b_p, b_n, g_p, g_n, K)
    handle = o.minimize(nz_expr)
    o.set("timeout", args.timeout * 1000)
    t0 = time.monotonic()
    r = o.check()
    elapsed = time.monotonic() - t0
    print(f"  Z3 Optimize: {r}  ({elapsed:.2f}s)")
    if r == sat:
        m = o.model()
        nz_val = m.eval(nz_expr).as_long()
        adds = nz_val - (2*K + M)
        alpha, beta, gamma = extract_model(m, a_p, a_n, b_p, b_n, g_p, g_n, K)
        ok, fail = verify_witness(alpha, beta, gamma, K)
        if not ok:
            print(f"  CROSS-CHECK FAILED: {fail}")
            return 1
        print(f"  Optimal Σ|nz| = {nz_val} ({adds} additions).")
        print_witness(alpha, beta, gamma, K, label="Z3 Optimize witness")
        return 0
    else:
        return 1


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    p_sweep = sub.add_parser("sweep")
    p_sweep.add_argument("--floor", type=int, default=30)
    p_sweep.add_argument("--ceiling", type=int, default=36)
    p_sweep.add_argument("--timeout", type=int, default=600)
    p_sweep.set_defaults(func=cmd_sweep)

    p_at = sub.add_parser("at")
    p_at.add_argument("--threshold", type=int, required=True)
    p_at.add_argument("--timeout", type=int, default=600)
    p_at.set_defaults(func=cmd_at)

    p_opt = sub.add_parser("optimize")
    p_opt.add_argument("--timeout", type=int, default=1800)
    p_opt.set_defaults(func=cmd_optimize)

    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
