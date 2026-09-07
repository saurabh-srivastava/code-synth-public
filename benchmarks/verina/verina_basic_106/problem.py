"""verina_basic_106 (arraySum) — VERINA-basic port.

Pointwise element-wise sum of two integer arrays: C[k] = A[k] + B[k]
for k in [0, n).  Identical shape to `add_arrays`; a three-array
transform where A and B are read-only inputs and C is the output.

VERINA source (source of truth):
  signature : arraySum (a : Array Int) (b : Array Int) -> Array Int
  precond   : a.size = b.size
  code      : c := Array.mkArray n 0; loop i in [0, n):
              c := c.set! i (a[i]! + b[i]!)   -- reads originals a[i], b[i]
  postcond  : (result.size = a.size) ∧
              (∀ i, i < a.size → a[i]! + b[i]! = result[i]!)

Fidelity mapping:
  - VERINA `a : Array Int`      -> our input array A + length n.
  - VERINA `b : Array Int`      -> our input array B (same length n).
  - VERINA `result : Array Int` -> our output array C.
  - VERINA precond `a.size = b.size`
                                -> both A and B are indexed by the SAME
                                   length n; the equal-length premise is
                                   discharged structurally (one n for
                                   both), so it need not appear as a
                                   separate atom.  Our pre `n >= 0`
                                   captures the Nat-ness of a.size.
  - `result.size = a.size`      -> C has length n by construction (the
                                   SB()>>Loop>>SB() shape writes C[0..n)
                                   in place, preserving length).
  - `∀ i < a.size, a[i]! + b[i]! = result[i]!`
                                -> ForAll k. 0<=k<n => C[k] == A[k] + B[k].

VERINA reads the ORIGINAL elements a[i], b[i] when writing index i
(A and B are never mutated), so there is no read-before-write hazard:
our loop reads A[i], B[i] (inputs, never written) and writes C[i].

No auxiliary fold/sum/count function is referenced by the postcond,
so this is a PURE Z3 pointwise transform (no UF, no axioms).  The
`A[k] + B[k]` term appears identically on both sides of the inductive
step, so the obligation stays linear.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A and B and a length n (with n >= 0), "
        "populate a third integer array C so that C[k] equals A[k] + B[k] "
        "for every k in [0, n)."
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
                "C[k] == A[k] + B[k]))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "C[k] == A[k] + B[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"C": "Update(C, i, A[i] + B[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_106/lean/SynthLean/Y2Corpus/verina_basic_106",
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
