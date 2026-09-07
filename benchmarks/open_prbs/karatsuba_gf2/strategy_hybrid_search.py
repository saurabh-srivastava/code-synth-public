"""strategy_hybrid_search — Hybrid Z3 SAT + UF abstraction.

Searches for a polymul_5 algorithm at TARGET scalar-mult
cost using K_3 polymul_3 + K_2 polymul_2 UF "blocks" with
parametric L-matrix inputs and parametric γ-combiner outputs.

This is the **discovery-capable** counterpart to
strategy_a_n5_2way_prototype.py (which only verifies a
hand-coded recipe).  The synth framework's UF axioms give
inner structure to Z3's SAT search; the search variables
(L matrices, γ combiners) parameterize the algorithm space.

Architecture:
  - polymul_2, polymul_3 declared as UFs with their
    coefficient axioms (same as Strategy A).
  - For each "call slot" k ∈ [1..K]: declare boolean
    variables for the L_a^k, L_b^k matrices (n_inputs × call_arity
    bits per call) parameterizing the call's inputs.
  - For each output j ∈ [0, 2n-2]: declare γ_{j,k,c} bits
    parameterizing the linear combination over (call k,
    coefficient c) sub-mults.
  - Constraint: for all input vectors (a, b), the combining
    matches polymul_5(a, b).  This is **universal** over
    the GF(2)^n × GF(2)^n input space — encoded via
    tensor-equality constraints on the coefficient-tuple
    level.

Search dimensions (n=5):
  - K_3 polymul_3 calls: 2 · (3 · 5) = 30 L-bits per call.
  - K_2 polymul_2 calls: 2 · (2 · 5) = 20 L-bits per call.
  - 9 outputs × (5K_3 + 3K_2) γ-bits each.

For K_3=2, K_2=0 (target cost 2·R(3) = 12 mults):
  - L bits: 60.
  - γ bits: 9 × 10 = 90.
  - Total: 150 boolean variables.
  - Universal-over-input constraint: 9 · 5 · 5 = 225
    tensor-equality constraints (each over GF(2) ⊕ of
    triple products γ · L_a · L_b summed across call slots
    and coefficients).

If SAT: NEW RESULT — algorithm beating Cenk-Hasan's 13-mult
upper bound for R(5) over GF(2).  Verify against the spec
before claiming.

If UNSAT: 2·polymul_3 cannot achieve polymul_5; rules out
this subspace.  Doesn't prove R(5) ≥ 13 in general (would
need to also rule out 4·polymul_2, mixed combos, etc.),
but narrows the search.

If TIMEOUT: search budget exceeded; try larger budget,
stronger symmetry breaking, or different parameter
allocation.
"""
from z3 import (And, Bool, BoolVal, If, Not, Or, Solver,
                Xor, sat, unsat, set_param)
import sys
import time


# Defaults; overridden by CLI flag --n
N = 5      # inputs per side (deg-(N-1) polynomial)
M = 2 * N - 1   # output coefficients


# --- polymul_2 / polymul_3 coefficient formulas (over GF(2)) ---

def polymul_1_coeff(p, q, c):
    """polymul_1: scalar bilinear product.  Arity 1, 1 coefficient.
    p = (p0,); q = (q0,); c = 0."""
    if c == 0:   return And(p[0], q[0])
    raise ValueError(c)


def polymul_2_coeff(p, q, c):
    """Symbolic GF(2)-coefficient of polymul_2(p, q) at index c.
    p = (p0, p1); q = (q0, q1); c ∈ {0, 1, 2}.
    Each pᵢ, qᵢ is a Boolean (∈ GF(2))."""
    if c == 0:   return And(p[0], q[0])
    if c == 1:   return Xor(And(p[0], q[1]), And(p[1], q[0]))
    if c == 2:   return And(p[1], q[1])
    raise ValueError(c)


def polymul_3_coeff(p, q, c):
    """GF(2)-coefficient of polymul_3(p, q) at index c, p,q ∈ GF(2)^3."""
    if c == 0:   return And(p[0], q[0])
    if c == 1:   return Xor(And(p[0], q[1]), And(p[1], q[0]))
    if c == 2:   return Xor(Xor(And(p[0], q[2]), And(p[1], q[1])),
                            And(p[2], q[0]))
    if c == 3:   return Xor(And(p[1], q[2]), And(p[2], q[1]))
    if c == 4:   return And(p[2], q[2])
    raise ValueError(c)


# Per-call config: (arity, n_coeffs, coeff_fn).
_CALL_TYPES = {
    "p1": (1, 1, polymul_1_coeff),  # rank-1 scalar product (cost R(1)=1)
    "p2": (2, 3, polymul_2_coeff),  # rank-3 (cost R(2)=3)
    "p3": (3, 5, polymul_3_coeff),  # rank-5 (cost R(3)=6)
}


def target_tensor(n=None):
    """T[j][i][k] = 1 iff a_i·b_k contributes to polymul_n output j."""
    if n is None:
        n = N
    m = 2 * n - 1
    T = [[[0] * n for _ in range(n)] for _ in range(m)]
    for j in range(m):
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


def encode_search(call_kinds, n_inputs=None, n_outputs=None, sym_break=True):
    if n_inputs is None:
        n_inputs = N
    if n_outputs is None:
        n_outputs = 2 * n_inputs - 1
    """Build a search formula for a polymul_5 algorithm
    using the given call_kinds list (each ∈ {'p2', 'p3'})."""
    solver = Solver()
    K = len(call_kinds)

    # L_a[k][i_arg][i_input]: bit-matrix mapping
    #   input-coefficient a_{i_input} → call k's arg position i_arg.
    L_a = []
    L_b = []
    coeff_count = []
    for k, kind in enumerate(call_kinds):
        arity, n_coeffs, _ = _CALL_TYPES[kind]
        coeff_count.append(n_coeffs)
        L_a.append([[Bool(f"La_{k}_{j}_{i}") for i in range(n_inputs)]
                    for j in range(arity)])
        L_b.append([[Bool(f"Lb_{k}_{j}_{i}") for i in range(n_inputs)]
                    for j in range(arity)])

    T = target_tensor(n_inputs)

    # γ[j_output][k_call][c_coeff]: contributes coefficient c of
    # call k's output to polymul_5 output j.
    gamma = [[[Bool(f"g_{j}_{k}_{c}") for c in range(coeff_count[k])]
              for k in range(K)] for j in range(n_outputs)]

    # Universal-over-inputs constraint, expressed via tensor equality.
    # For each (j, i, k_input), require:
    #   ⊕ [over (k_call, c_coeff)] γ[j][k][c] · σ(call k, c, i, k_input)
    #   ≡ T[j][i][k_input]  (mod 2)
    #
    # where σ(call k, c, i, k_input) = 1 iff a_i · b_{k_input} appears
    # in the (k, c) sub-mult.  σ is determined by the L matrices.

    # σ(k, c, i, k_input) = ⊕_{j_a, j_b s.t. (j_a, j_b) contributes to c}
    #                       L_a[k][j_a][i] · L_b[k][j_b][k_input]
    #
    # The "contributes" pattern depends on call kind:
    #   polymul_2 coefficient c:
    #     c=0: (0,0); c=1: (0,1) ⊕ (1,0); c=2: (1,1)
    #   polymul_3 coefficient c:
    #     c=0: (0,0); c=1: (0,1)⊕(1,0);
    #     c=2: (0,2)⊕(1,1)⊕(2,0); c=3: (1,2)⊕(2,1); c=4: (2,2)
    coeff_patterns = {
        "p1": {0: [(0, 0)]},
        "p2": {0: [(0, 0)],
               1: [(0, 1), (1, 0)],
               2: [(1, 1)]},
        "p3": {0: [(0, 0)],
               1: [(0, 1), (1, 0)],
               2: [(0, 2), (1, 1), (2, 0)],
               3: [(1, 2), (2, 1)],
               4: [(2, 2)]},
    }

    def sigma(k_call, c, i_input, k_input):
        """Whether a_{i_input} · b_{k_input} contributes to (k_call, c)."""
        kind = call_kinds[k_call]
        pattern = coeff_patterns[kind][c]
        terms = []
        for (j_a, j_b) in pattern:
            terms.append(And(L_a[k_call][j_a][i_input],
                             L_b[k_call][j_b][k_input]))
        return xor_all(terms)

    # Add tensor-equality constraints.
    for j in range(n_outputs):
        for i in range(n_inputs):
            for k_input in range(n_inputs):
                # ⊕ over (k_call, c_coeff) of γ · σ.
                terms = []
                for k_call in range(K):
                    for c in range(coeff_count[k_call]):
                        terms.append(And(gamma[j][k_call][c],
                                         sigma(k_call, c, i, k_input)))
                xor = xor_all(terms)
                target = T[j][i][k_input]
                if target == 1:
                    solver.add(xor)
                else:
                    solver.add(Not(xor))

    # Each call must be non-trivial: at least one bit in each L row.
    for k in range(K):
        arity, _, _ = _CALL_TYPES[call_kinds[k]]
        for j in range(arity):
            solver.add(Or(*L_a[k][j]))
            solver.add(Or(*L_b[k][j]))

    if sym_break and len(set(call_kinds)) == 1:
        # If all calls are the same kind, lex-order them.
        for k in range(K - 1):
            sig_k = sum([row for row in L_a[k]], []) + \
                    sum([row for row in L_b[k]], [])
            sig_kp1 = sum([row for row in L_a[k+1]], []) + \
                      sum([row for row in L_b[k+1]], [])
            # Lex: sig_k ≤ sig_kp1.
            result = BoolVal(False)
            eq_so_far = BoolVal(True)
            for a, b in zip(sig_k, sig_kp1):
                result = Or(result, And(eq_so_far, Not(a), b))
                eq_so_far = And(eq_so_far, a == b)
            solver.add(Or(result, eq_so_far))

    return solver, L_a, L_b, gamma


def search(call_kinds, n_inputs=None, timeout_s=600, sym_break=True):
    if n_inputs is None:
        n_inputs = N
    n_outputs = 2 * n_inputs - 1
    set_param("parallel.enable", True)

    cost_per_kind = {"p1": 1, "p2": 3, "p3": 6}
    total_cost = sum(cost_per_kind[k] for k in call_kinds)
    print(f"\nHybrid search at n={n_inputs}: {call_kinds} config.")
    print(f"  Total scalar-mult cost: {total_cost}")
    naive_cost = n_inputs * n_inputs
    print(f"  (vs naive {naive_cost})")

    solver, L_a, L_b, gamma = encode_search(
        call_kinds, n_inputs=n_inputs, n_outputs=n_outputs,
        sym_break=sym_break)
    solver.set("timeout", timeout_s * 1000)

    n_la = sum(len(call_kinds) * _CALL_TYPES[k][0] * N
               for k in set(call_kinds)
               for _ in [None]) // len(set(call_kinds)) \
           if call_kinds else 0
    # Simpler boolean variable count:
    n_la_bits = sum(_CALL_TYPES[k][0] * n_inputs for k in call_kinds)
    n_lb_bits = n_la_bits
    n_gamma_bits = n_outputs * sum(_CALL_TYPES[k][1] for k in call_kinds)
    n_constraints = n_outputs * n_inputs * n_inputs
    print(f"  Search variables: {n_la_bits + n_lb_bits + n_gamma_bits} "
          f"booleans ({n_la_bits} La, {n_lb_bits} Lb, {n_gamma_bits} γ)")
    print(f"  Tensor-equality constraints: {n_constraints}")
    print(f"  Symmetry breaking: {'lex-order same-kind' if sym_break else 'none'}")
    print(f"  Timeout: {timeout_s}s")

    t0 = time.monotonic()
    result = solver.check()
    elapsed = time.monotonic() - t0
    print(f"\n  Z3 result: {result}  ({elapsed:.1f}s)")

    if result == sat:
        model = solver.model()
        print(f"\n=== Discovered algorithm: {call_kinds}, cost = {total_cost} ===")
        for k, kind in enumerate(call_kinds):
            arity, n_coeffs, _ = _CALL_TYPES[kind]
            a_combos = []
            for j_a in range(arity):
                bits = [int(bool(model[L_a[k][j_a][i]])) for i in range(n_inputs)]
                terms = [f"a{i}" for i in range(n_inputs) if bits[i]]
                a_combos.append(" + ".join(terms) or "0")
            b_combos = []
            for j_b in range(arity):
                bits = [int(bool(model[L_b[k][j_b][i]])) for i in range(n_inputs)]
                terms = [f"b{i}" for i in range(n_inputs) if bits[i]]
                b_combos.append(" + ".join(terms) or "0")
            args = ", ".join(a_combos + b_combos)
            print(f"  m{k} = {kind}({args})   [{n_coeffs} coefficients]")
        print()
        for j in range(n_outputs):
            terms = []
            for k_call in range(len(call_kinds)):
                _, n_coeffs, _ = _CALL_TYPES[call_kinds[k_call]]
                for c in range(n_coeffs):
                    if bool(model[gamma[j][k_call][c]]):
                        terms.append(f"m{k_call}[{c}]")
            combo = " ⊕ ".join(terms) or "0"
            print(f"  r{j} = {combo}")
        published_R = {2: 3, 3: 6, 4: 9, 5: 13, 6: 17, 7: 22}
        target = published_R.get(n_inputs, -1)
        print(f"\n*** SAT: polymul_{n_inputs} in {total_cost} "
              f"scalar mults (published R({n_inputs}) ≈ {target}). ***")
        if 0 < target and total_cost < target:
            print(f"    BEATS published bound!  Verify the discovered "
                  f"algorithm against literature (Cenk-Hasan, Bernstein, "
                  f"Montgomery) before claiming novelty.")
        return 0
    elif result == unsat:
        print(f"\n*** UNSAT: configuration {call_kinds} (cost "
              f"{total_cost}) cannot compute polymul_5. ***")
        return 0
    else:
        print(f"\n*** TIMEOUT: search budget exceeded.  Try longer "
              f"timeout or different parameter allocation. ***")
        return 1


def main():
    # Usage: hybrid_search.py CONFIG [TIMEOUT [n_inputs]]
    # CONFIG: comma-separated calls (e.g., "p3,p3,p2" or "p2,p2,p2").
    if len(sys.argv) >= 2:
        cfg = sys.argv[1].split(",")
        call_kinds = []
        for spec in cfg:
            kind = spec.strip().lower()
            if kind.startswith("p3"):
                n = int(kind[2:]) if len(kind) > 2 else 1
                call_kinds.extend(["p3"] * n)
            elif kind.startswith("p2"):
                n = int(kind[2:]) if len(kind) > 2 else 1
                call_kinds.extend(["p2"] * n)
            elif kind.startswith("p1"):
                n = int(kind[2:]) if len(kind) > 2 else 1
                call_kinds.extend(["p1"] * n)
            else:
                raise SystemExit(f"Bad kind: {kind} (expected p1/p2/p3 or p1N etc.)")
        timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 600
        n_in = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    else:
        call_kinds = ["p3", "p3"]
        timeout = 600
        n_in = 5

    return search(call_kinds, n_inputs=n_in, timeout_s=timeout)


if __name__ == "__main__":
    sys.exit(main())
