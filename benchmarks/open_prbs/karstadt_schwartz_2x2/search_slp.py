"""search_slp.py — search for K=7 SLP-encoded 2×2 matmul algorithms
with bounded total addition count (L_A + L_B + L_G).

The SLP encoding allows shared intermediate sub-expressions, so a
single addition operation feeds multiple bilinear products.  This
captures the Karstadt-Schwartz model.

Usage:
  python search_slp.py --total 12  [--la 4 --lb 4 --lg 4] [--timeout 600]
  python search_slp.py --total 11
  python search_slp.py --total 15  # sanity: should match Winograd

We sweep over splits (L_A, L_B, L_G) that sum to `total`, since the
distribution between sides isn't fixed a priori.
"""
import argparse
import sys
import time
from z3 import sat, unsat, set_param

sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/karstadt_schwartz_2x2')
from encoding_slp import encode_slp


K = 7


def search_split(L_A, L_B, L_G, timeout_s):
    """Search for K=7 SLP with given split.  Returns (verdict, elapsed)."""
    set_param("parallel.enable", True)
    solver, _ = encode_slp(K, L_A, L_B, L_G)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    r = solver.check()
    elapsed = time.monotonic() - t0
    if r == sat:
        return "sat", elapsed, solver.model()
    elif r == unsat:
        return "unsat", elapsed, None
    else:
        return "timeout", elapsed, None


def enumerate_splits(total):
    """Enumerate (L_A, L_B, L_G) with sum == total.  By A↔B symmetry,
    only enumerate L_A ≤ L_B.  L_G is constrained ≥ 0."""
    splits = []
    for L_A in range(0, total + 1):
        for L_B in range(L_A, total - L_A + 1):
            L_G = total - L_A - L_B
            if L_G < 0:
                continue
            splits.append((L_A, L_B, L_G))
    return splits


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--total", type=int, required=True,
                   help="Total additions budget = L_A + L_B + L_G")
    p.add_argument("--la", type=int, default=None,
                   help="Fix L_A (skip sweep)")
    p.add_argument("--lb", type=int, default=None,
                   help="Fix L_B")
    p.add_argument("--lg", type=int, default=None,
                   help="Fix L_G")
    p.add_argument("--timeout", type=int, default=300,
                   help="Per-split timeout (s)")
    args = p.parse_args()

    if args.la is not None and args.lb is not None and args.lg is not None:
        splits = [(args.la, args.lb, args.lg)]
    else:
        splits = enumerate_splits(args.total)

    print(f"SLP search: K={K}, total additions = {args.total}.")
    print(f"  Enumerating {len(splits)} splits.")
    print(f"  Per-split timeout: {args.timeout}s.\n")

    sat_found = []
    for L_A, L_B, L_G in splits:
        # Heuristic guard: SLP with very small L_A may be infeasible
        # (need at least enough adds to reach 7 distinct linear forms
        # on both sides + 4 outputs).
        if L_A + N_A_BASE < K_NEEDED or L_B + N_B_BASE < K_NEEDED:
            print(f"  [LA={L_A}, LB={L_B}, LG={L_G}]  SKIP (insufficient sources)")
            continue
        verdict, elapsed, model = search_split(L_A, L_B, L_G, args.timeout)
        print(f"  [LA={L_A}, LB={L_B}, LG={L_G}]  {verdict:<8}  ({elapsed:.2f}s)")
        sys.stdout.flush()
        if verdict == "sat":
            sat_found.append((L_A, L_B, L_G, elapsed))
            print(f"    *** SAT at total = {args.total} (split {L_A}+{L_B}+{L_G}) ***")
            # Don't break — log all SAT splits.

    print()
    if sat_found:
        print(f"Result: total = {args.total} SAT in {len(sat_found)} split(s):")
        for la, lb, lg, t in sat_found:
            print(f"  L_A={la}, L_B={lb}, L_G={lg}  ({t:.2f}s)")
        return 0
    else:
        print(f"Result: total = {args.total} UNSAT/TIMEOUT across all splits.")
        return 1


# Heuristic constants — we need at least 4 distinct base sources
# usable as left/right factors for 7 mults.  With L_A intermediates
# and 4 base inputs, we have 4+L_A available sources for left factors.
# Each of 7 mults picks one; they need not be distinct, but if every
# m_k.left is the SAME source, the algorithm can't span the input
# space.  We don't enforce this directly; just guard against
# pathological splits.
N_A_BASE = 4
N_B_BASE = 4
K_NEEDED = 1   # at minimum each side has 1 source available


if __name__ == "__main__":
    sys.exit(main())
