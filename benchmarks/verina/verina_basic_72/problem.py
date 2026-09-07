"""verina_basic_72 (append) — VERINA-basic port.

Append a scalar to the end of an array: the result is `a` with `b`
written as the new last element.  VERINA's reference code copies
`a[0..n)` into a fresh buffer (recursive `copy`) and then pushes `b`.
This is a pointwise array-copy followed by a single trailing write, so
it is PURE Z3 with a quantified prefix invariant — no UF, no axioms.
Shape mirrors `array_copy` (fresh output buffer `C` filled in a loop),
with an extra final SB writing the appended element `C[n] := b`.

VERINA source (source of truth):
  signature : append (a : Array Int) (b : Int) -> Array Int
  precond   : True   (no preconditions; array may be empty)
  code      : let c_initial := copy a 0 Array.empty   -- copies a[0..size)
              let c_full     := c_initial.push b       -- appends b
              c_full
  postcond  : (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!))
              ∧ result[a.size]! = b
              ∧ result.size = a.size + 1

Fidelity mapping:
  - VERINA `a : Array Int`      -> our read-only input array `A` + a
                                   length `n` modelling `a.size`.
  - VERINA `b : Int`            -> our scalar input `b`.
  - VERINA `result : Array Int` -> our output buffer `C` (declared as
                                   both an input buffer and the output,
                                   exactly like `B` in `array_copy`).
  - `∀ i ∈ range' 0 a.size, result[i]! = a[i]!`
                                -> ForAll k. 0<=k<n => C[k]==A[k]
                                   (the copied prefix).
  - `result[a.size]! = b`       -> C[n] == b  (the appended element,
                                   written by the final SB at index n).
  - `result.size = a.size + 1`  -> NOT asserted: our arrays are unbounded
                                   Z3 maps with no explicit `.size` field.
                                   The size claim is captured STRUCTURALLY
                                   instead — the synthesized code writes
                                   exactly indices 0..n-1 (loop) and n
                                   (final SB), i.e. the first n+1 slots, so
                                   the logical length is a.size+1 by
                                   construction.  (Same size-abstraction
                                   convention as verina_basic_13 /
                                   verina_basic_56 / array_copy.)
  - VERINA `True` precond       -> our `n >= 0` (n models a.size, a Nat,
                                   hence implicitly >= 0).

No auxiliary fold/sum/count/product function is referenced by the
postcondition, so no UF is introduced — pure Z3.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n (n >= 0), a fresh output "
        "buffer C, and a scalar b, produce the append of b onto A: copy "
        "A[0..n) into C, then write C[n] := b.  Afterwards C[k]==A[k] for "
        "every k in [0, n) and C[n]==b."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("C", "int[]", "input"),        # fresh output buffer
                Var("n", "int", "input"),          # models a.size
                Var("b", "int", "input")],         # scalar to append
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "n >= 0",
    post     = (
        # copied prefix: C[0..n) mirrors A[0..n)
        "ForAll(lambda k: Implies(0 <= k and k < n, C[k] == A[k])) and "
        # appended element sits at index n
        "(C[n] == b)"
    ),

    atoms = {
        # Init: copy cursor at 0.
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            # First i slots already copied.
            "ForAll(lambda k: Implies(0 <= k and k < i, C[k] == A[k]))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Body: C[i] := A[i]; i := i + 1.
        "s@B1": [{"C": "Update(C, i, A[i])", "i": "i + 1"}],

        # Final: write the appended element at index n.
        "s@B2": [{"C": "Update(C, n, b)"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_72/lean/SynthLean/Y2Corpus/verina_basic_72",
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
