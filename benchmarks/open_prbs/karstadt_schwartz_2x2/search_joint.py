"""search_joint.py — driver for joint bilinear + SLP search.

Goals:
  - Sanity: total = 18 with split (5, 5, 8) should be SAT (Strassen).
  - Heun-equivalent: total = 15, sweep splits.
  - Karstadt-Schwartz: total = 12, sweep splits.

Usage:
  python search_joint.py sanity                # (5, 5, 8), expect SAT
  python search_joint.py at --la 5 --lb 5 --lg 8 --timeout 600
  python search_joint.py sweep --total 18 --timeout 600
"""
import argparse
import sys

sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/karstadt_schwartz_2x2')
from encoding_joint import search_joint, sweep_total, K
from encoding import verify_witness, print_witness


def cmd_at(args):
    print(f"Joint search at L_A={args.la}, L_B={args.lb}, L_G={args.lg} "
          f"(total {args.la + args.lb + args.lg}).")
    verdict, elapsed, witness = search_joint(args.la, args.lb, args.lg,
                                             args.timeout, verbose=True)
    print(f"\n  Z3: {verdict}  ({elapsed:.2f}s)")
    if verdict == "sat":
        alpha, beta, gamma = witness
        ok, fail = verify_witness(alpha, beta, gamma, K)
        if not ok:
            print(f"  CROSS-CHECK FAILED: {fail}")
            return 1
        print_witness(alpha, beta, gamma, K,
                      label=f"joint SLP {args.la}+{args.lb}+{args.lg}")
    return 0


def cmd_sanity(args):
    print("Sanity joint search at (5, 5, 8) = 18 (Strassen total).")
    args.la, args.lb, args.lg = 5, 5, 8
    args.timeout = args.timeout or 600
    return cmd_at(args)


def cmd_sweep(args):
    sat = sweep_total(args.total, args.timeout, ordered=args.balanced)
    if sat:
        print(f"\nResult: total = {args.total} SAT in {len(sat)} splits.")
        return 0
    print(f"\nResult: total = {args.total} UNSAT/TIMEOUT across all splits.")
    return 1


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    p_sanity = sub.add_parser("sanity")
    p_sanity.add_argument("--timeout", type=int, default=600)
    p_sanity.set_defaults(func=cmd_sanity)

    p_at = sub.add_parser("at")
    p_at.add_argument("--la", type=int, required=True)
    p_at.add_argument("--lb", type=int, required=True)
    p_at.add_argument("--lg", type=int, required=True)
    p_at.add_argument("--timeout", type=int, default=600)
    p_at.set_defaults(func=cmd_at)

    p_sweep = sub.add_parser("sweep")
    p_sweep.add_argument("--total", type=int, required=True)
    p_sweep.add_argument("--timeout", type=int, default=600)
    p_sweep.add_argument("--balanced", action="store_true",
                         help="Try balanced splits first")
    p_sweep.set_defaults(func=cmd_sweep)

    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
