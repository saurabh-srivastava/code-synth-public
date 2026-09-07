"""search.py — branchless code synthesis driver.

Targets concrete specs and sweeps slot counts to find the minimum
SLP length.
"""
import argparse
import sys
import time
from z3 import sat, unsat, set_param

sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/branchless_codegen')
from encoding import (
    encode_slp, extract_slp, verify_slp, print_slp, simulate_slp,
)


# Library of target specs.  Each entry: (name, num_inputs, W, spec_func, known_min, notes).
SPECS = {
    # abs(x) for signed W-bit:
    #   y = If(x < 0, -x, x)
    # Known minimum on 8-bit: 3 ops (Hacker's Delight).
    "abs8": {
        "W": 8, "num_inputs": 1,
        "spec": lambda x: x if (x & 0x80) == 0 else (-x & 0xFF),
        "known_min": 3,
        "notes": "abs(x) for 8-bit signed.  Known min 3 (HD).",
    },
    "abs4": {
        "W": 4, "num_inputs": 1,
        "spec": lambda x: x if (x & 0x8) == 0 else (-x & 0xF),
        "known_min": 3,
        "notes": "abs(x) for 4-bit signed.  Warmup.",
    },
    # sign(x) returns -1, 0, +1 (as W-bit signed):
    "sign4": {
        "W": 4, "num_inputs": 1,
        "spec": lambda x: 0 if x == 0 else (1 if (x & 0x8) == 0 else 0xF),
        "known_min": 4,
        "notes": "sign(x) for 4-bit signed.  Returns -1 (0xF), 0, +1.",
    },
    # min(a, b) for unsigned W-bit:
    "min4u": {
        "W": 4, "num_inputs": 2,
        "spec": lambda a, b: min(a, b),
        "known_min": 4,
        "notes": "min(a, b) unsigned 4-bit.  Branchless min has 4-op form.",
    },
    # max(a, b) for unsigned W-bit:
    "max4u": {
        "W": 4, "num_inputs": 2,
        "spec": lambda a, b: max(a, b),
        "known_min": 4,
        "notes": "max(a, b) unsigned 4-bit.",
    },
    # XOR-swap (single output: a XOR b is the obvious 1-op):
    # (skip - trivial)
    # parity(x) for 8-bit: 1 iff popcount(x) is odd.
    "parity8": {
        "W": 8, "num_inputs": 1,
        "spec": lambda x: bin(x).count("1") & 1,
        "known_min": None,  # 3 XORs minimum (log2(8) tree)
        "notes": "Parity of 8-bit value.  Tree of 3 XORs minimum.",
    },
    # popcount(x) for 4-bit:
    "popcount4": {
        "W": 4, "num_inputs": 1,
        "spec": lambda x: bin(x).count("1"),
        "known_min": None,
        "notes": "popcount of 4-bit value.  Output in [0, 4].",
    },
    # Average-without-overflow: avg(a, b) = (a + b) / 2, correct
    # for all unsigned a, b without intermediate overflow.
    # HD recipe: (a & b) + ((a ^ b) >> 1)  → 4 ops.
    "avg4u": {
        "W": 4, "num_inputs": 2,
        "spec": lambda a, b: (a + b) >> 1,
        "known_min": None,
        "notes": "avg(a,b)=(a+b)/2 unsigned, no intermediate overflow.  HD 4 ops; sub-4 open?",
    },
    # isnonzero: returns 1 if x != 0 else 0.  HD: (x | -x) >>u (W-1).
    "isnonzero4": {
        "W": 4, "num_inputs": 1,
        "spec": lambda x: 1 if x != 0 else 0,
        "known_min": None,
        "notes": "1 if x != 0 else 0.  HD form: (x | -x) >>u (W-1).  3 ops.",
    },
    # iszero: returns 1 if x == 0 else 0.
    "iszero4": {
        "W": 4, "num_inputs": 1,
        "spec": lambda x: 1 if x == 0 else 0,
        "known_min": None,
        "notes": "1 if x == 0 else 0.  Dual of isnonzero.",
    },
    # Conditional negate: if mask is all-1s, return -x; else return x.
    # mask ∈ {0, -1 (all-ones)}.
    # HD form: (x XOR mask) - mask  → 2 ops (if mask is the "subtract-by" value).
    "cneg4": {
        "W": 4, "num_inputs": 2,
        "spec": lambda x, m: (x if (m & 0xF) == 0 else (-x & 0xF))
                              if (m & 0xF) in (0, 0xF) else 0,
        "known_min": None,
        "notes": "Conditional negate: m is 0 (keep) or 0xF (negate).  Don't-care otherwise.",
    },
    # Equal-to-zero pattern (Bit twiddle): -(x | -x) >> (W-1) for unsigned.
}


def cmd_at(args):
    if args.spec not in SPECS:
        print(f"Unknown spec: {args.spec}.  Known: {sorted(SPECS)}")
        return 1
    cfg = SPECS[args.spec]
    print(f"Spec '{args.spec}': W={cfg['W']}, num_inputs={cfg['num_inputs']}")
    print(f"  Note: {cfg['notes']}")
    print(f"  Search C={args.C}, timeout {args.timeout}s.")

    set_param("parallel.enable", True)
    solver, op_picks, src1_picks, src2_picks = encode_slp(
        cfg["W"], args.C, cfg["spec"], num_inputs=cfg["num_inputs"])
    solver.set("timeout", args.timeout * 1000)
    t0 = time.monotonic()
    r = solver.check()
    elapsed = time.monotonic() - t0
    print(f"\n  Z3: {r}  ({elapsed:.2f}s)")
    if r == sat:
        slp = extract_slp(solver.model(), op_picks, src1_picks, src2_picks,
                          args.C, cfg["num_inputs"])
        ok, fail = verify_slp(slp, cfg["spec"], cfg["W"], cfg["num_inputs"])
        if not ok:
            print(f"  CROSS-CHECK FAILED: input {fail[0]} → got {fail[1]}, want {fail[2]}")
            return 1
        print_slp(slp, cfg["num_inputs"], label=f"{args.spec} at C={args.C}")
        return 0
    elif r == unsat:
        print(f"  *** UNSAT: no {args.C}-slot SLP computes '{args.spec}'. ***")
        return 0
    return 1


def cmd_sweep(args):
    if args.spec not in SPECS:
        print(f"Unknown spec: {args.spec}.  Known: {sorted(SPECS)}")
        return 1
    cfg = SPECS[args.spec]
    print(f"Sweep '{args.spec}': W={cfg['W']}, num_inputs={cfg['num_inputs']}")
    print(f"  Sweep C ∈ [{args.C_min}, {args.C_max}].  Per-C timeout {args.timeout}s.\n")
    set_param("parallel.enable", True)
    print(f"  {'C':>3} {'verdict':<9} {'time':>9}")
    print(f"  {'-'*3} {'-'*9} {'-'*9}")
    sat_at = None
    sat_slp = None
    for C in range(args.C_min, args.C_max + 1):
        solver, op_picks, src1_picks, src2_picks = encode_slp(
            cfg["W"], C, cfg["spec"], num_inputs=cfg["num_inputs"])
        solver.set("timeout", args.timeout * 1000)
        t0 = time.monotonic()
        r = solver.check()
        elapsed = time.monotonic() - t0
        print(f"  {C:>3} {str(r):<9} {elapsed:>8.2f}s")
        sys.stdout.flush()
        if r == sat:
            sat_at = C
            sat_slp = extract_slp(solver.model(), op_picks, src1_picks,
                                  src2_picks, C, cfg["num_inputs"])
            break
        elif r != unsat:
            print(f"  *** TIMEOUT at C={C}; aborting. ***")
            break
    if sat_at is not None:
        ok, fail = verify_slp(sat_slp, cfg["spec"], cfg["W"], cfg["num_inputs"])
        if not ok:
            print(f"  CROSS-CHECK FAILED at C={sat_at}: {fail}")
            return 1
        print_slp(sat_slp, cfg["num_inputs"],
                  label=f"Minimum SLP for '{args.spec}': C={sat_at}")
    return 0


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    p_at = sub.add_parser("at")
    p_at.add_argument("--spec", type=str, required=True)
    p_at.add_argument("--C", type=int, required=True)
    p_at.add_argument("--timeout", type=int, default=300)
    p_at.set_defaults(func=cmd_at)

    p_sweep = sub.add_parser("sweep")
    p_sweep.add_argument("--spec", type=str, required=True)
    p_sweep.add_argument("--C-min", type=int, default=1)
    p_sweep.add_argument("--C-max", type=int, default=6)
    p_sweep.add_argument("--timeout", type=int, default=300)
    p_sweep.set_defaults(func=cmd_sweep)

    p_list = sub.add_parser("list")
    p_list.set_defaults(func=lambda a: (
        print("Available specs:"),
        [print(f"  {k}: {v['notes']}") for k, v in SPECS.items()],
        0)[2])

    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
