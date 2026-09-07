"""verina_basic_30 (elementWiseModulo) — VERINA-basic port.

Pointwise element-wise modulo of two integer arrays:
  R[k] = A[k] % B[k]  for k in [0, n).
Same shape as `add_arrays` (two read-only input arrays A, B written
into a third array R), but the pointwise transform is the modulo of
the corresponding elements instead of their sum.

VERINA source (source of truth):
  signature : elementWiseModulo (a : Array Int) (b : Array Int) -> Array Int
  precond   : a.size = b.size ∧ a.size > 0 ∧ (∀ i, i < b.size → b[i]! ≠ 0)
  code      : a.mapIdx (fun i x => x % b[i]!)
  postcond  : (result.size = a.size) ∧
              (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)

Fidelity mapping:
  - VERINA `a : Array Int`      -> our input array A + length n.
  - VERINA `b : Array Int`      -> our input array B.
  - VERINA `result : Array Int` -> our output array R.
  - `a.size = b.size`           -> both A and B are indexed by the same
                                   single length n (a single `n` models
                                   both sizes, so equality is structural).
  - `a.size > 0`                -> our `n > 0`.
  - `∀ i < b.size, b[i]! ≠ 0`   -> ForAll k. 0<=k<n => B[k] != 0
                                   (models the non-zero-divisor precond;
                                   Nat index bound i < b.size becomes
                                   0<=k<n over our int index).
  - `result.size = a.size`      -> R has length n by construction (the
                                   SB()>>Loop>>SB() shape writes R[0..n)
                                   in place, preserving length).
  - `∀ i < result.size, result[i]! = a[i]! % b[i]!`
                                -> ForAll k. 0<=k<n => R[k] == A[k] % B[k].

The modulo term A[k] % B[k] appears identically on both sides of the
inductive step (the store writes exactly `A[i] % B[i]`, the invariant
reads it back), so Z3 treats it congruently as a Store/Select round-
trip — no reasoning about modulo's arithmetic semantics is required.
Our `%` translates to Z3's integer `mod` (SMT-LIB Euclidean), which is
the same "modulo of corresponding elements" the VERINA postcond and
reference code both denote; the correspondence is exact at the operator
level.  No auxiliary fold/sum/count/product function is referenced, so
this is a PURE Z3 pointwise transform (no UF, no axioms).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A and B and a length n (with n > 0 and "
        "every B[k] non-zero), populate a third integer array R so that "
        "R[k] equals A[k] % B[k] for every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("R", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("R", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = ("n > 0 and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] != 0))"),
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, "
                "R[k] == A[k] % B[k]))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "R[k] == A[k] % B[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"R": "Update(R, i, A[i] % B[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_30/lean/SynthLean/Y2Corpus/verina_basic_30",
    wedge_threshold = 200,
    solver_timeout_ms = 120_000,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
