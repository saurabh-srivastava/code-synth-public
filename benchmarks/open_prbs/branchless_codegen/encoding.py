"""encoding.py — branchless straight-line code synthesis via Z3 BV.

Searches for a fixed-length SLP that computes a target bitvector
specification.  Each slot is one primitive operation over earlier
wires.  Final slot's output must equal the spec for all inputs.

Op alphabet (single-bitwidth W):
  1-arg ops:  NEG (-x), NOT (~x), SAR_W1 (x >>s (W-1)), SHL (x << 1)
  2-arg ops:  ADD, SUB, XOR, AND, OR, SHR_LOGICAL (a >>u b)

Each slot k ∈ [0, C):
  - op_choice: 1-hot over the alphabet (currently 10 ops).
  - src1: 1-hot over {x, s_0, s_1, ..., s_{k-1}}  (size k+1).
  - src2: 1-hot over same set; ignored if op is 1-arg.

The slot's output is a Z3 BV expression of width W.

Correctness: exhaustive check over x ∈ {0, ..., 2^W - 1}.
For each concrete x_val:
  - Substitute x_val into the symbolic SLP expression for slot C-1.
  - Assert it equals spec(x_val).

This avoids Z3 quantifier instantiation, which can wedge on BV
ForAll for richer specs.  For small W (≤ 10) exhaustive is trivial.
"""
from itertools import combinations
from z3 import (And, Bool, BoolVal, BitVec, BitVecVal, Extract,
                If, Not, Or, PbEq, Solver, Sum,
                LShR, sat, unsat, set_param, simplify)


# Operation alphabet: each is (name, arity, lambda(args, W) → BV expr).
#
# Arity-1 ops include 0-arg "constant" ops that ignore their arg
# (CONST_0, CONST_1) — the slot still allocates a src1 pick by
# the encoding, but the op's lambda ignores it.
OPS = [
    ("CONST_0", 1, lambda args, W: BitVecVal(0, W)),
    ("CONST_1", 1, lambda args, W: BitVecVal(1, W)),
    ("NEG",    1, lambda args, W: -args[0]),
    ("NOT",    1, lambda args, W: ~args[0]),
    ("SAR_W1", 1, lambda args, W: args[0] >> BitVecVal(W - 1, W)),
    ("SHL1",   1, lambda args, W: args[0] << BitVecVal(1, W)),
    ("SHR1",   1, lambda args, W: LShR(args[0], BitVecVal(1, W))),
    ("SHL2",   1, lambda args, W: args[0] << BitVecVal(2, W)),
    ("SHR2",   1, lambda args, W: LShR(args[0], BitVecVal(2, W))),
    ("SHR4",   1, lambda args, W: LShR(args[0], BitVecVal(4, W)) if W >= 5 else BitVecVal(0, W)),
    ("ADD",    2, lambda args, W: args[0] + args[1]),
    ("SUB",    2, lambda args, W: args[0] - args[1]),
    ("XOR",    2, lambda args, W: args[0] ^ args[1]),
    ("AND",    2, lambda args, W: args[0] & args[1]),
    ("OR",     2, lambda args, W: args[0] | args[1]),
    ("LSHR",   2, lambda args, W: LShR(args[0], args[1])),
]
NUM_OPS = len(OPS)


def encode_slp(W, C, spec_func, num_inputs=1, sym_break=True):
    """Build Z3 search for a C-step SLP over BV width W that
    computes `spec_func` from `num_inputs` BV inputs.

    spec_func(*xs) returns the expected output for inputs xs (each
    of width W).  Inputs are concrete Python ints in [0, 2^W).

    Returns (solver, op_picks, src_picks).
    """
    solver = Solver()

    # Per slot: 1-hot op choice.
    op_picks = [[Bool(f"op_{k}_{o}") for o in range(NUM_OPS)]
                for k in range(C)]
    for k in range(C):
        solver.add(PbEq([(op_picks[k][o], 1) for o in range(NUM_OPS)], 1))

    # Per slot: 1-hot src picks over {x_0, ..., x_{num_inputs-1}, s_0, ..., s_{k-1}}.
    # Source count at slot k = num_inputs + k.
    src1_picks = []
    src2_picks = []
    for k in range(C):
        n_src = num_inputs + k
        s1 = [Bool(f"src1_{k}_{s}") for s in range(n_src)]
        s2 = [Bool(f"src2_{k}_{s}") for s in range(n_src)]
        solver.add(PbEq([(s1[s], 1) for s in range(n_src)], 1))
        solver.add(PbEq([(s2[s], 1) for s in range(n_src)], 1))
        src1_picks.append(s1)
        src2_picks.append(s2)

    # Symmetry breaking.
    if sym_break:
        # The final slot's output is THE output; no later slot
        # consumes it.  So we can force the final slot to depend
        # on at least one prior wire (the last source pick).
        # (Trivial: PbEq already forces a pick.)
        pass

    # Correctness check: exhaustive over all 2^W input values per input.
    # For multi-input specs, enumerate the Cartesian product.
    import itertools
    input_grid = list(itertools.product(*([range(2**W)] * num_inputs)))

    def slot_expr(k, x_vals):
        """Compute s_k's BV expression at concrete input vector x_vals,
        as a Z3 BV expression (parametric in op_picks / src_picks)."""
        # Build the list of source BV expressions: x_0..x_{num_inputs-1}, s_0..s_{k-1}.
        wires = [BitVecVal(x_vals[i], W) for i in range(num_inputs)]
        for j in range(k):
            wires.append(slot_cache[(j, x_vals)])
        # Pick src1 / src2 via 1-hot.
        n_src = num_inputs + k
        src1_val = wires[0]
        for s in range(1, n_src):
            src1_val = If(src1_picks[k][s], wires[s], src1_val)
        src2_val = wires[0]
        for s in range(1, n_src):
            src2_val = If(src2_picks[k][s], wires[s], src2_val)
        # Pick op via 1-hot: build nested If across all ops.
        result = OPS[0][2]([src1_val, src2_val], W)
        for o in range(1, NUM_OPS):
            result = If(op_picks[k][o], OPS[o][2]([src1_val, src2_val], W), result)
        return result

    # Cache slot expressions per input vector.
    slot_cache = {}
    for x_vals in input_grid:
        for k in range(C):
            slot_cache[(k, x_vals)] = slot_expr(k, x_vals)
        # Final slot's output must equal spec(x_vals).
        expected = BitVecVal(spec_func(*x_vals) & ((1 << W) - 1), W)
        solver.add(slot_cache[(C - 1, x_vals)] == expected)

    return solver, op_picks, src1_picks, src2_picks


def extract_slp(model, op_picks, src1_picks, src2_picks, C, num_inputs):
    """Extract the SLP as a list of (op_name, src1, src2) tuples."""
    slp = []
    for k in range(C):
        op_idx = next(o for o in range(NUM_OPS)
                      if model[op_picks[k][o]] is not None
                      and bool(model[op_picks[k][o]]))
        op_name, arity, _ = OPS[op_idx]
        n_src = num_inputs + k
        src1 = next(s for s in range(n_src)
                    if model[src1_picks[k][s]] is not None
                    and bool(model[src1_picks[k][s]]))
        if arity == 2:
            src2 = next(s for s in range(n_src)
                        if model[src2_picks[k][s]] is not None
                        and bool(model[src2_picks[k][s]]))
        else:
            src2 = None
        slp.append((op_name, src1, src2))
    return slp


def simulate_slp(slp, x_vals, W, num_inputs):
    """Run an SLP on concrete inputs.  Returns the final slot's value
    (truncated to W bits)."""
    mask = (1 << W) - 1
    wires = list(x_vals)
    for op_name, src1, src2 in slp:
        a = wires[src1]
        b = wires[src2] if src2 is not None else 0
        if op_name == "CONST_0": v = 0
        elif op_name == "CONST_1": v = 1
        elif op_name == "NEG":   v = (-a) & mask
        elif op_name == "NOT": v = (~a) & mask
        elif op_name == "SAR_W1":
            sign_bit = (a >> (W - 1)) & 1
            v = (mask if sign_bit else 0)
        elif op_name == "SHL1": v = (a << 1) & mask
        elif op_name == "SHR1": v = (a >> 1) & mask
        elif op_name == "SHL2": v = (a << 2) & mask
        elif op_name == "SHR2": v = (a >> 2) & mask
        elif op_name == "SHR4": v = (a >> 4) & mask if W >= 5 else 0
        elif op_name == "ADD": v = (a + b) & mask
        elif op_name == "SUB": v = (a - b) & mask
        elif op_name == "XOR": v = (a ^ b) & mask
        elif op_name == "AND": v = (a & b) & mask
        elif op_name == "OR":  v = (a | b) & mask
        elif op_name == "LSHR":
            shift = b & ((1 << W) - 1)
            if shift >= W: v = 0
            else: v = (a >> shift) & mask
        else:
            raise ValueError(f"Unknown op: {op_name}")
        wires.append(v)
    return wires[-1]


def verify_slp(slp, spec_func, W, num_inputs=1):
    """Check that `slp` computes `spec_func` on all 2^W inputs per input."""
    import itertools
    mask = (1 << W) - 1
    for x_vals in itertools.product(*([range(2**W)] * num_inputs)):
        got = simulate_slp(slp, x_vals, W, num_inputs)
        want = spec_func(*x_vals) & mask
        if got != want:
            return False, (x_vals, got, want)
    return True, None


def print_slp(slp, num_inputs, label=""):
    """Pretty-print an SLP."""
    if label:
        print(f"\n=== {label} ===")
    print(f"  Inputs: {num_inputs}, slots: {len(slp)}")
    input_names = [f"x{i}" for i in range(num_inputs)]
    for k, (op_name, src1, src2) in enumerate(slp):
        names = input_names + [f"s{j}" for j in range(k)]
        n1 = names[src1]
        if src2 is not None:
            n2 = names[src2]
            print(f"    s{k} = {op_name}({n1}, {n2})")
        else:
            print(f"    s{k} = {op_name}({n1})")
