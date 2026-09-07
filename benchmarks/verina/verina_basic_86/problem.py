"""verina_basic_86 — rotate (VERINA-basic port).

Rotate an integer array left by `offset`: the output element at
index i is the input element at index `(i + offset) mod n`, where
n is the array size.  A pure copy-into-fresh-array loop — the
`array_copy` shape (`SB() >> Loop(SB())`) with the read index
changed from `A[i]` to `A[(i + offset) % n]`.  Pointwise permutation
transform => pure Z3, no uninterpreted function / axioms needed.

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_86/):
    signature : rotate (a : Array Int) (offset : Int) : Array Int
    precond   : offset ≥ 0
    code      : b0 := mkArray n default; for i in 0..n:
                    b[i] := a[Int.toNat ((i + offset) % n)]
    postcond  : result.size = a.size ∧
                (∀ i, i < a.size →
                   result[i]! = a[Int.toNat ((Int.ofNat i + offset)
                                             % (Int.ofNat a.size))]!)

Fidelity mapping:
    a       : Array Int -> input array `A` (read-only).
    offset  : Int       -> input `offset`, VERINA precond `offset ≥ 0`.
    n = a.size          -> input `n` with the implied `n >= 0`
                           (array size is nonnegative; the empty
                           array is n = 0).
    result  : Array Int -> output array `B`.

    precond `offset ≥ 0`      -> pre clause `offset >= 0`.
    postcond
      `result.size = a.size`  -> implicit: like every array
          benchmark in this corpus, arrays are total Z3 functions
          and "size" is carried by the quantifier bound `0<=k<n`;
          the loop writes exactly B[0..n), so the modelled portion
          has the same length n as A.  (Empty array n=0 => vacuous.)
      `∀ i < a.size, result[i] = a[Int.toNat((i+offset)%a.size)]`
                              -> post: `ForAll k: 0<=k<n =>
                                 B[k] == A[(k + offset) % n]`.

    On `Int.toNat ((i + offset) % n)`: for every modelled index we
    have k >= 0, offset >= 0 (precond) and n >= 1 (forced by
    `0 <= k < n`), so the dividend `k + offset >= 0` and divisor
    `n > 0`; Lean's `Int.%` (emod) then lands in `[0, n)` and
    `Int.toNat` is the identity there.  Z3's `%` on the same
    nonnegative dividend / positive divisor lands in the same
    `[0, n)`, so `A[(k+offset)%n]` faithfully models
    `a[Int.toNat((k+offset)%n)]`.  The n=0 (empty) case is covered:
    the quantifier is vacuous, so the mod value is never required.

    No auxiliary fold/sum/count/product is referenced, so no UF /
    axiom is introduced — pure-Z3 synthesis.

Spec:
    Pre  : offset >= 0 ∧ n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  B[k] == A[(k + offset) % n]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of size n (n >= 0) and a "
        "non-negative offset, produce array B such that B[k] equals "
        "A[(k + offset) mod n] for every k in 0..n-1 (a left rotation "
        "by offset)."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("offset", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "(offset >= 0) and (n >= 0)",
    post     = ("ForAll(lambda k: Implies("
                "0 <= k and k < n, B[k] == A[(k + offset) % n]))"),

    atoms = {
        # Init: i := 0.
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, B[k] == A[(k + offset) % n]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Body: B[i] := A[(i + offset) % n]; i := i + 1.
        "s@B1": [{"B": "Update(B, i, A[(i + offset) % n])",
                  "i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_86/lean/SynthLean/Y2Corpus/verina_basic_86",
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
