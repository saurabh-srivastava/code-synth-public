"""verina_basic_85 (reverse) — VERINA-basic port.

Reverse an integer array: produce an output whose element at index i is
the input's element at index (size - 1 - i).  This is a pure permutation
/ pointwise-read transform (each output slot is a single indexed read of
the source), so it is PURE Z3 with ONE quantified prefix invariant — no
UF, no axioms.  Shape mirrors `array_copy`: a read-only source array `A`
and a DISTINCT output array `R`, filled left-to-right by a single loop.

VERINA source (source of truth):
  signature : reverse (a : Array Int) -> Array Int
  precond   : True   (no preconditions)
  code      : reverse_core a 0, where
                reverse_core arr i =
                  if i < arr.size / 2 then
                    let j := arr.size - 1 - i
                    swap arr[i], arr[j]; reverse_core arr'' (i+1)
                  else arr
              (i.e. an in-place two-pointer swap reverse)
  postcond  : (result.size = a.size)
              ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)

Fidelity mapping
----------------
  - VERINA `a : Array Int`           -> our read-only input array `A`.
  - VERINA `a.size` (Nat)            -> our int input `n`, with the Nat
                                        non-negativity `n >= 0` carried as
                                        the precondition (VERINA's precond is
                                        `True`; a size is a Nat, hence >= 0,
                                        so `n >= 0` is the faithful residue —
                                        it does not restrict any real input).
  - VERINA `result`                  -> our output array `R`.  We write to a
                                        DISTINCT fresh array `R` rather than
                                        reversing `A` in place; both satisfy
                                        the identical functional postcondition
                                        below.  The spec (pre/post) is the
                                        source of truth, and the synthesizer
                                        finds its own code, so a copy-based
                                        reverse is a faithful realization of
                                        the SAME postcond as VERINA's in-place
                                        reference code.
  - `∀ i < a.size. result[i]! = a[a.size - 1 - i]!`
                                     -> ForAll k. 0 <= k < n =>
                                        R[k] == A[n - 1 - k].
                                        VERINA's `a.size - 1 - i` (Nat) maps
                                        to `n - 1 - k`; for 0 <= k < n this is
                                        an in-range index (n-1-k in [0, n-1]),
                                        so Nat-vs-int subtraction agrees.
  - `result.size = a.size`           -> dropped as an explicit atom: our
                                        arrays are unbounded Z3 maps (no
                                        reified `.size`), and the loop fills
                                        exactly R[0 .. n-1], so length
                                        preservation holds by construction —
                                        same convention as array_copy /
                                        verina_basic_56_copy / swap_first_last.

No auxiliary fold/sum/count/product function is referenced by the
postcondition, so no UF is introduced — pure Z3.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n (n >= 0), produce an "
        "output array R that is A reversed: R[k] takes the value "
        "A[n - 1 - k] for every k in 0..n-1."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("R", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("R", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "n >= 0",
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, "
                "R[k] == A[n - 1 - k]))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "R[k] == A[n - 1 - k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Body: R[i] := A[n - 1 - i]; i := i + 1
        "s@B1": [{"R": "Update(R, i, A[n - 1 - i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_85/lean/SynthLean/Y2Corpus/verina_basic_85",
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
