"""search.py — sorting-network search driver.

Tries SAT at C comparators, descending from C_max, to find minimum C.
"""
import argparse
import sys
import time
from z3 import sat, unsat, set_param

sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/sorting_networks')
from encoding import (
    encode_network, extract_network, verify_network, print_network,
)


def check_at(N, C, timeout_s, sym_break=True):
    set_param("parallel.enable", True)
    solver, has = encode_network(N, C, sym_break=sym_break)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    r = solver.check()
    elapsed = time.monotonic() - t0
    if r == sat:
        return "sat", elapsed, extract_network(solver.model(), has, N, C)
    elif r == unsat:
        return "unsat", elapsed, None
    else:
        return "timeout", elapsed, None


def cmd_at(args):
    print(f"N={args.N}, C={args.C}, timeout {args.timeout}s, "
          f"sym_break={not args.no_sym_break}")
    verdict, elapsed, network = check_at(args.N, args.C, args.timeout,
                                          sym_break=not args.no_sym_break)
    print(f"\n  Z3: {verdict}  ({elapsed:.2f}s)")
    if verdict == "sat":
        ok, fail = verify_network(network, args.N)
        if not ok:
            x, out = fail
            print(f"  CROSS-CHECK FAILED: input {x} → {out}")
            return 1
        print_network(network, args.N,
                      label=f"Sorting network for N={args.N}, C={args.C}")
        return 0
    elif verdict == "unsat":
        print(f"  *** N={args.N}, C={args.C} is UNSAT (no sorting network). ***")
        return 0
    return 1


def cmd_sweep(args):
    """Sweep C from C_max DOWN to C_min; first UNSAT is one above minimum."""
    print(f"Sweep N={args.N}, C ∈ [{args.C_min}, {args.C_max}].")
    print(f"  Per-C timeout: {args.timeout}s\n")
    print(f"  {'C':>4} {'verdict':<9} {'time':>8}")
    print(f"  {'-'*4} {'-'*9} {'-'*8}")
    last_sat = None
    last_sat_network = None
    for C in range(args.C_max, args.C_min - 1, -1):
        verdict, elapsed, network = check_at(args.N, C, args.timeout)
        print(f"  {C:>4} {verdict:<9} {elapsed:>7.2f}s")
        sys.stdout.flush()
        if verdict == "sat":
            last_sat = C
            last_sat_network = network
        elif verdict == "unsat":
            print(f"\n  *** UNSAT at C={C}; minimum sorting network has "
                  f"≥ {C+1} comparators. ***")
            if last_sat is not None:
                print(f"  Last SAT: C={last_sat}.")
            break
        elif verdict == "timeout":
            print(f"\n  *** TIMEOUT at C={C}; aborting. ***")
            break
    if last_sat_network is not None:
        ok, fail = verify_network(last_sat_network, args.N)
        if ok:
            print_network(last_sat_network, args.N,
                          label=f"Min-known SAT witness C={last_sat}")
    return 0


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    p_at = sub.add_parser("at")
    p_at.add_argument("--N", type=int, required=True)
    p_at.add_argument("--C", type=int, required=True)
    p_at.add_argument("--timeout", type=int, default=300)
    p_at.add_argument("--no-sym-break", action="store_true")
    p_at.set_defaults(func=cmd_at)

    p_sweep = sub.add_parser("sweep")
    p_sweep.add_argument("--N", type=int, required=True)
    p_sweep.add_argument("--C-min", type=int, required=True)
    p_sweep.add_argument("--C-max", type=int, required=True)
    p_sweep.add_argument("--timeout", type=int, default=300)
    p_sweep.set_defaults(func=cmd_sweep)

    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
