"""verina_basic_105 (arrayProduct) — VERINA-basic port.

Pointwise element-wise product of two integer arrays into a third:
C[k] = A[k] * B[k] for k in [0, n).  Same shape as `add_arrays`
(two read-only inputs A, B; one output C), but the pointwise
transform is a product rather than a sum.

VERINA source (source of truth):
  signature : arrayProduct (a : Array Int) (b : Array Int) -> Array Int
  precond   : a.size = b.size
  code      : len := a.size; c := mkArray len 0;
              loop over i in [0, len): c := set! c i (a[i]! * b[i]!)
  postcond  : (result.size = a.size) ∧
              (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)

Fidelity mapping:
  - VERINA `a : Array Int`, `b : Array Int`  -> our input arrays A, B
                                                + a shared length n.
  - VERINA precond `a.size = b.size`         -> both A and B are read
                                                with the SAME length n;
                                                equal-length is thus a
                                                structural given, and we
                                                add `n >= 0` (n models a
                                                Nat size, hence >= 0).
  - VERINA `result : Array Int`              -> our output array C.
  - `result.size = a.size`                   -> C has length n by
                                                construction (the
                                                SB()>>Loop>>SB() shape
                                                writes C[0..n) in place,
                                                preserving length).
  - `∀ i < a.size, a[i]! * b[i]! = result[i]!`
                                             -> ForAll k. 0<=k<n =>
                                                C[k] == A[k]*B[k].

The VERINA implementation defaults missing indices to 0 (the
`if i < a.size then a[i]! else 0` guards), but the postcondition is
stated only over `i < a.size` under the `a.size = b.size` precond,
so within-bounds every access is real — the equal-length model
captures the postcond exactly.

No auxiliary fold/sum/count/product accumulator is referenced by the
postcond (this is a POINTWISE transform, not a prefix-product), so
this is a PURE Z3 benchmark — no UF, no axioms.  The product term
A[k]*B[k] appears identically on both sides of the inductive step,
so it is treated congruently — no nonlinear search required.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A and B and an output integer array "
        "C, all of length n (with n >= 0), populate C so that C[k] "
        "equals A[k] * B[k] for every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("C", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, "
                "C[k] == A[k] * B[k]))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "C[k] == A[k] * B[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"C": "Update(C, i, A[i] * B[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_105/lean/SynthLean/Y2Corpus/verina_basic_105",
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
