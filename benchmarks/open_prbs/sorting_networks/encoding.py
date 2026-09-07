"""encoding.py — sorting-network search encoding via 0/1 principle.

A sorting network on N wires is a fixed sequence of compare-exchange
operations:
    CE(i, j):  (w[i], w[j])  ←  (min(w[i], w[j]), max(w[i], w[j]))

For 0/1-valued wires, min = AND and max = OR.  The 0/1 principle:
a comparator network sorts every input iff it sorts every input in
{0, 1}^N.  So correctness reduces to a Boolean SAT problem.

Encoding (for N wires, C comparator slots):
  - For each slot k ∈ [0, C), 1-hot choice over the P = N(N-1)/2
    ordered pairs (i, j) with i < j.  Booleans `has[k][p]`.
  - For each x ∈ {0, 1}^N, simulate the network: introduce wire
    booleans w_{x, k, i} for step k and wire i after k operations.
    Constrain:
       w_{x, k+1, i} = OR over pair choices p = (a, b) of:
          - has[k][p] ∧ AND(w_{x,k,a}, w_{x,k,b})       if a == i
          - has[k][p] ∧ OR(w_{x,k,a}, w_{x,k,b})        if b == i
          - has[k][p] ∧ w_{x, k, i}                     if i ∉ {a, b}
  - Final sortedness: for all x, for all 0 ≤ i < N-1:
       w_{x, C, i}  ⇒  w_{x, C, i+1}

Symmetry break (subnetwork commutativity):
  - Consecutive comparators with disjoint wire sets commute → lex
    order their pair indices.
  - The first comparator can be canonicalized to start from wire 0
    (since renaming wires preserves sortedness).  Not used by default;
    too aggressive in general.
"""
from itertools import combinations
from z3 import (And, Bool, BoolVal, Implies, Not, Or, PbEq, Solver,
                Sum, sat, unsat, set_param)


def pairs_of(N):
    """All (i, j) with 0 ≤ i < j < N, in lex order."""
    return list(combinations(range(N), 2))


def encode_network(N, C, sym_break=True):
    """Build Z3 search for a sorting network on N wires with C
    comparator slots.

    Returns (solver, has) where `has[k][p]` is the boolean for "slot
    k picks pair p" (p indexes into pairs_of(N))."""
    solver = Solver()
    pairs = pairs_of(N)
    P = len(pairs)

    # 1-hot pair selection per slot.
    has = [[Bool(f"has_{k}_{p}") for p in range(P)] for k in range(C)]
    for k in range(C):
        solver.add(PbEq([(has[k][p], 1) for p in range(P)], 1))

    # Propagate for each x ∈ {0, 1}^N.
    for x_idx in range(2 ** N):
        x = [(x_idx >> i) & 1 for i in range(N)]
        w_prev = [BoolVal(x[i] == 1) for i in range(N)]
        for k in range(C):
            w_next = [Bool(f"w_{x_idx}_{k+1}_{i}") for i in range(N)]
            for i in range(N):
                clauses = []
                for p_idx, (a, b) in enumerate(pairs):
                    if a == i:
                        # i is the "min" wire of pair → AND of inputs.
                        clauses.append(And(has[k][p_idx],
                                           w_prev[a], w_prev[b]))
                    elif b == i:
                        # i is the "max" wire of pair → OR of inputs.
                        clauses.append(And(has[k][p_idx],
                                           Or(w_prev[a], w_prev[b])))
                    else:
                        # i untouched by slot k.
                        clauses.append(And(has[k][p_idx], w_prev[i]))
                solver.add(w_next[i] == Or(*clauses))
            w_prev = w_next

        # Sortedness at the end: w[i] ⇒ w[i+1] for all i.
        for i in range(N - 1):
            solver.add(Implies(w_prev[i], w_prev[i+1]))

    if sym_break:
        # Disjoint-wire-set commutativity: consecutive comparators
        # with disjoint wires must have pair_index[k] < pair_index[k+1].
        # Forbid out-of-order pairs when wires are disjoint.
        for k in range(C - 1):
            for p1_idx in range(P):
                a1, b1 = pairs[p1_idx]
                for p2_idx in range(p1_idx):  # p2 < p1
                    a2, b2 = pairs[p2_idx]
                    # Are pairs disjoint?
                    if a1 not in (a2, b2) and b1 not in (a2, b2):
                        # has[k][p1] AND has[k+1][p2] is forbidden
                        # (out-of-order disjoint pair).
                        solver.add(Not(And(has[k][p1_idx],
                                           has[k+1][p2_idx])))

        # First-comparator canonicalization: WLOG the first comparator
        # is (0, 1).  Wire renaming preserves sortedness, so any sorting
        # network has an isomorphic copy with this first move.
        first_pair_idx = pairs.index((0, 1))
        solver.add(has[0][first_pair_idx])

    return solver, has


def extract_network(model, has, N, C):
    """Extract the (i, j) sequence from a satisfying model."""
    pairs = pairs_of(N)
    network = []
    for k in range(C):
        for p_idx, (a, b) in enumerate(pairs):
            val = model[has[k][p_idx]]
            if val is not None and bool(val):
                network.append((a, b))
                break
    return network


def simulate_network(network, x, N):
    """Simulate a network on a single input x (tuple of 0/1).  Returns
    the final wire values."""
    w = list(x)
    for (a, b) in network:
        if w[a] > w[b]:
            w[a], w[b] = w[b], w[a]
    return tuple(w)


def verify_network(network, N):
    """Verify a network sorts ALL inputs in {0, 1}^N."""
    for x_idx in range(2 ** N):
        x = tuple((x_idx >> i) & 1 for i in range(N))
        out = simulate_network(network, x, N)
        if any(out[i] > out[i+1] for i in range(N-1)):
            return False, (x, out)
    return True, None


def print_network(network, N, label=""):
    if label:
        print(f"\n=== {label} ===")
    print(f"  N = {N}, comparators = {len(network)}")
    for k, (a, b) in enumerate(network):
        print(f"    CE_{k:2d}: ({a}, {b})")
