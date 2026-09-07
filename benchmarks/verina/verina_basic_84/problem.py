"""verina_basic_84 (replace) — VERINA-basic port.

Conditional pointwise transform: replace every element greater than a
threshold k with -1, leave every other element unchanged.  The loop
body is an SB(n=2) (if A[i] > k, write -1; else copy A[i]).  Same
shape as `clamp_array_positive` (per-element conditional writing the
output array in both branches).

VERINA source (source of truth):
  signature : replace (arr : Array Int) (k : Int) -> Array Int
  precond   : True   (no preconditions; array may be empty)
  code      : replace_loop arr k 0 arr, where the recursive helper,
              for each i in [0, arr.size), reads the ORIGINAL element
              oldArr[i]! and sets acc := acc.set! i (-1) when
              oldArr[i]! > k, else leaves acc[i] unchanged.  (The
              accumulator starts as arr, so untouched slots keep their
              original value.)
  postcond  : (result.size = arr.size) ∧
              (∀ i, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
              (∀ i, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))

Fidelity mapping:
  - VERINA `arr : Array Int`     -> our input array A + length n.
  - VERINA `k : Int` (threshold) -> our input scalar k.
  - VERINA `result : Array Int`  -> our output array B.
  - `result.size = arr.size`     -> B has length n by construction
                                    (the SB()>>Loop>>SB() shape writes
                                    B[0..n) in place, preserving length).
  - `∀ i < arr.size, arr[i]! > k → result[i]! = -1`
        AND
    `∀ i < arr.size, arr[i]! ≤ k → result[i]! = arr[i]!`
                                 -> a single ForAll case-split:
                                    (A[j] >  k → B[j] == -1) AND
                                    (A[j] <= k → B[j] == A[j]),
                                    written as the equivalent disjunction
                                    ((A[j] > k and B[j] == -1) or
                                     (A[j] <= k and B[j] == A[j])).
  - VERINA `True` precond        -> our `n >= 0` (n models arr.size, a
                                    Nat, hence implicitly >= 0).

VERINA reads the ORIGINAL element (oldArr[i]) when deciding index i, so
no read-before-write hazard: our loop reads A[i] (input, never mutated)
and writes B[i], which is the same semantics.  The reference is an
in-place update starting from a copy of arr; modelling it as a distinct
output array B is semantically identical because the postcond relates
result solely to the ORIGINAL arr.

No auxiliary fold/sum/count function is referenced by the postcond, so
this is a PURE Z3 conditional pointwise transform (no UF, no axioms).
The transform terms appear identically on both sides of the inductive
step, so the obligation stays linear.

Note: the threshold parameter is named `k`, so the ForAll bound
variable is `j` (avoiding a name collision with the input).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, an integer array B, a length n "
        "(with n >= 0), and a threshold k, populate B so that B[j] "
        "equals -1 when A[j] > k, and equals A[j] otherwise, for "
        "every j in [0, n)."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input"),
                Var("k", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda j: Implies(0 <= j and j < n, "
                "((A[j] > k and B[j] == -1) or "
                " (A[j] <= k and B[j] == A[j]))))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda j: Implies(0 <= j and j < i, "
             "((A[j] > k and B[j] == -1) or "
             " (A[j] <= k and B[j] == A[j]))))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Loop body: SB(n=2)
        # Branch 0: A[i] > k → B[i] := -1
        "g@B1.0": ["A[i] > k", "A[i] >= k + 1"],
        "s@B1.0": [{"B": "Update(B, i, -1)", "i": "i + 1"}],
        # Branch 1: A[i] <= k → B[i] := A[i]
        "g@B1.1": ["A[i] <= k", "A[i] < k + 1"],
        "s@B1.1": [{"B": "Update(B, i, A[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_84/lean/SynthLean/Y2Corpus/verina_basic_84",
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
