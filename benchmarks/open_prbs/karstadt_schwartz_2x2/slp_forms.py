"""slp_forms.py — minimum-SLP search for a fixed set of ±1 linear forms.

Given N target linear forms over D base inputs (each entry ∈ {-1, 0, +1}),
find the minimum number of binary ±1 additions needed to compute them all
in a single straight-line program with shared intermediates.

This is the "shortest derivation chain for multiple bilinear forms"
subproblem — directly relevant to Karstadt-Schwartz's 12-add count.

Encoding (linear in booleans → QF_LIA, no NIA):
  - L candidate intermediate sums s_0, ..., s_{L-1}.  Each s_l picks
    two sources from {base_0..base_{D-1}, s_0..s_{l-1}} with signs.
  - For each target form F_n, a 1-hot output picker selects which
    source (base or intermediate) equals F_n, with a sign.
  - All unfolded coefficient values are Int but bounded by the SLP
    depth (each binary add doubles the worst-case magnitude).
  - Constraint: each base coef of s_l, when unfolded, computes its
    actual ±1-or-larger value; the output picker forces the
    selected source's unfolded vector to match F_n exactly.

Usage:
  forms = [(1,0,0,1), (0,0,1,1), (1,0,0,0), ...]   # left factors of Strassen
  cost, slp = min_slp(forms, max_L=10, timeout=300)
"""
import sys
import time
from z3 import (And, Bool, BoolVal, If, Int, Not, Or, Solver,
                Sum, Xor, sat, unsat, set_param)


def encode_slp_for_forms(forms, L, D):
    """Build Z3 search for SLP of length L computing all target `forms`
    over D base inputs.

    Returns (solver, intermediate_choices, target_picks).
    """
    solver = Solver()
    N = len(forms)

    # ---- Each intermediate s_l: choose src1, src2 ∈ {0..D+l-1}, signs.
    intermediates = []  # list of coef-vectors (each a list of D Int exprs)
    int_choices = []
    for l in range(L):
        n_src = D + l
        src1 = Int(f"s_src1_{l}")
        src2 = Int(f"s_src2_{l}")
        sgn1 = Bool(f"s_sgn1_{l}")
        sgn2 = Bool(f"s_sgn2_{l}")
        solver.add(src1 >= 0, src1 < n_src)
        solver.add(src2 >= 0, src2 < n_src)
        solver.add(src1 < src2)  # break commutativity + force distinct

        # Available sources for unfolding.
        def base_vec(i):
            return [1 if k == i else 0 for k in range(D)]
        available = [base_vec(i) for i in range(D)] + intermediates[:]

        coef_vec = []
        for entry_idx in range(D):
            v1_terms = []
            for choice in range(n_src):
                src_coef = available[choice][entry_idx]
                # src_coef can be Int or int.
                v1_terms.append(
                    If(src1 == choice,
                       If(sgn1, -src_coef, src_coef),
                       0))
            v2_terms = []
            for choice in range(n_src):
                src_coef = available[choice][entry_idx]
                v2_terms.append(
                    If(src2 == choice,
                       If(sgn2, -src_coef, src_coef),
                       0))
            coef_vec.append(Sum(v1_terms) + Sum(v2_terms))
        intermediates.append(coef_vec)
        int_choices.append((src1, src2, sgn1, sgn2))

    # ---- Each target form F_n: pick a source (base or intermediate) +
    # sign, constrain unfolded coefs == F_n's coefs.
    target_picks = []
    def base_vec(i):
        return [1 if k == i else 0 for k in range(D)]
    all_sources = [base_vec(i) for i in range(D)] + intermediates[:]
    total_sources = D + L

    for n, target in enumerate(forms):
        pick = Int(f"t_pick_{n}")
        pick_sgn = Bool(f"t_sgn_{n}")
        solver.add(pick >= 0, pick < total_sources)

        for entry_idx in range(D):
            terms = []
            for choice in range(total_sources):
                src_coef = all_sources[choice][entry_idx]
                terms.append(
                    If(pick == choice,
                       If(pick_sgn, -src_coef, src_coef),
                       0))
            solver.add(Sum(terms) == target[entry_idx])
        target_picks.append((pick, pick_sgn))

    return solver, int_choices, target_picks, intermediates


def min_slp(forms, max_L=12, D=None, timeout_s=300, verbose=True):
    """Find minimum L such that all `forms` are computable with L SLP
    intermediates.  Sweep L from 0 upward; first SAT is the minimum.

    Returns (cost, model_info) or (None, None) on no-fit within max_L.
    """
    if D is None:
        D = len(forms[0]) if forms else 0
    if verbose:
        N = len(forms)
        print(f"slp_forms: search min SLP for N={N} forms over D={D} inputs.")
        print(f"  Sweeping L ∈ [0, {max_L}]; per-L timeout {timeout_s}s.")

    set_param("parallel.enable", True)
    for L in range(0, max_L + 1):
        solver, _, _, _ = encode_slp_for_forms(forms, L, D)
        solver.set("timeout", timeout_s * 1000)
        t0 = time.monotonic()
        r = solver.check()
        elapsed = time.monotonic() - t0
        if verbose:
            print(f"  L={L:>2}  {str(r):<10}  ({elapsed:.2f}s)")
            sys.stdout.flush()
        if r == sat:
            return L, solver.model()
        elif r == unknown if False else False:  # never the keyword; ignore
            pass
        if r != sat and r != unsat:
            # timeout, stop sweep
            if verbose:
                print(f"  TIMEOUT at L={L}.")
            return None, None
    return None, None


# Test: Strassen's 7 left factors over 4 inputs (a, b, c, d).
STRASSEN_LEFT = [
    (1, 0, 0, 1),   # m0: a + d
    (0, 0, 1, 1),   # m1: c + d
    (1, 0, 0, 0),   # m2: a
    (0, 0, 0, 1),   # m3: d
    (1, 1, 0, 0),   # m4: a + b
    (-1, 0, 1, 0),  # m5: -a + c
    (0, 1, 0, -1),  # m6: b - d
]
# Expected min SLP: 5 (each non-atom form needs 1 binary add;
# atoms a, d are free; no nontrivial sharing possible here).

STRASSEN_RIGHT = [
    (1, 0, 0, 1),   # m0: e + h
    (1, 0, 0, 0),   # m1: e
    (0, 1, 0, -1),  # m2: f - h
    (-1, 0, 1, 0),  # m3: -e + g
    (0, 0, 0, 1),   # m4: h
    (1, 1, 0, 0),   # m5: e + f
    (0, 0, 1, 1),   # m6: g + h
]
# Expected: 5.

STRASSEN_OUTPUT = [
    (1, 0, 0, 1, -1, 0, 1),  # c00 = m0 + m3 - m4 + m6
    (0, 0, 1, 0, 1, 0, 0),   # c01 = m2 + m4
    (0, 1, 0, 1, 0, 0, 0),   # c10 = m1 + m3
    (1, -1, 1, 0, 0, 1, 0),  # c11 = m0 - m1 + m2 + m5
]
# Expected: 8 (3 + 1 + 1 + 3 if no sharing; check whether sharing helps).


def main():
    print("=== Strassen left factors ===")
    cost_L, _ = min_slp(STRASSEN_LEFT, max_L=8, D=4, timeout_s=120)
    print(f"  Min SLP cost on Strassen-left: {cost_L}")

    print("\n=== Strassen right factors ===")
    cost_R, _ = min_slp(STRASSEN_RIGHT, max_L=8, D=4, timeout_s=120)
    print(f"  Min SLP cost on Strassen-right: {cost_R}")

    print("\n=== Strassen output combiners ===")
    cost_G, _ = min_slp(STRASSEN_OUTPUT, max_L=10, D=7, timeout_s=120)
    print(f"  Min SLP cost on Strassen-output: {cost_G}")

    if cost_L is not None and cost_R is not None and cost_G is not None:
        total = cost_L + cost_R + cost_G
        print(f"\n  Total SLP cost for Strassen 1969: {total}")
        print(f"  (Standard count: 18.)")


if __name__ == "__main__":
    main()
