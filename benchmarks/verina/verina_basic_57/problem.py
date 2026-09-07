"""verina_basic_57_count_less_than — VERINA-basic port (CountLessThan).

Ported from VERINA task `verina_basic_57` (CountLessThan; upstream
Clover `count_lessthan`).  Count how many elements of an integer
array are strictly less than a given threshold.

VERINA signature (source of truth):
    CountLessThan(numbers : Array Int, threshold : Int) -> Nat
VERINA precondition: True.
VERINA postcondition (source of truth, from task.lean):
    result - numbers.foldl (fun count n =>
                if n < threshold then count + 1 else count) 0 = 0 ∧
    numbers.foldl (...) 0 - result = 0
  i.e. (for Nat)  result = numbers.foldl
                    (fun count n => if n < threshold then count+1 else count) 0.

Framework encoding
------------------
    Pre  : n >= 0                        (n = numbers.size; a Nat, so n ≥ 0)
    Post : c == count_less(A, threshold, n)

`count_less : (Int → Int) → Int → Int → Int` is uninterpreted and
re-axiomatizes VERINA's left fold as a forward prefix recurrence:
  - count_less(A, threshold, 0)                       = 0            (empty prefix)
  - A[k] <  threshold ⇒ count_less(A, threshold, k+1) = count_less(A, threshold, k) + 1
  - A[k] >= threshold ⇒ count_less(A, threshold, k+1) = count_less(A, threshold, k)

Same shape as the corpus benchmarks `count_equal` (runtime-parameter
target) and `array_neg_count` (strict-inequality predicate); this is
literally `array_neg_count` with the fixed `0` bound generalised to a
runtime `threshold` input.

SPEC-FIDELITY NOTE
------------------
Our `count_less` axioms ARE the definitional unfolding of VERINA's
`Array.foldl` over the array prefix `A[0..k)`:
  * `count_less(A, threshold, 0) = 0` is the fold's initial
    accumulator `0` on the empty prefix.
  * the two step axioms are exactly the fold's step function
    `fun count n => if n < threshold then count + 1 else count`,
    specialised on the sign of `A[k] - threshold` (the `if` split).
`Array.foldl` folds left over indices `0,1,...,size-1`, adding 1
per element `< threshold`; our recurrence adds 1 at step `k` iff
`A[k] < threshold`.  Hence, by induction on the prefix length,
`count_less(A, threshold, n) = numbers.foldl (...) 0` when
`n = numbers.size`.  Therefore our post `c == count_less(A,
threshold, n)` is equivalent to VERINA's `result = foldl(...)`
(the `a-b=0 ∧ b-a=0` phrasing in task.lean is just `a = b` for Nat).

TRUST SURFACE: the three `count_less` axioms above (base + the two
per-branch step recurrences).  Everything else about the synthesized
loop (per-branch inductiveness, coverage, termination) is discharged
by the framework / Lean `.solved.lean` companions.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n (with n ≥ 0), and an "
        "integer threshold, count the number of elements among "
        "A[0], A[1], ..., A[n-1] that are strictly less than the "
        "threshold."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("threshold", "int", "input")],
    outputs  = [Var("c", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("count_less", ["int[]", "int", "int"], "int")],
    axioms = [
        "count_less(A, threshold, 0) == 0",
        ("ForAll(lambda k: Implies(k >= 0 and A[k] < threshold, "
         "count_less(A, threshold, k + 1) == "
         "count_less(A, threshold, k) + 1))"),
        ("ForAll(lambda k: Implies(k >= 0 and A[k] >= threshold, "
         "count_less(A, threshold, k + 1) == "
         "count_less(A, threshold, k)))"),
    ],

    pre  = "n >= 0",
    post = "c == count_less(A, threshold, n)",

    atoms = {
        "s@B0": [{"c": "0", "i": "0"}],

        "tau@L0": [
            "c == count_less(A, threshold, i)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] < threshold → c := c + 1, i := i + 1.
        "g@B1.0": ["A[i] < threshold"],
        "s@B1.0": [{"c": "c + 1", "i": "i + 1"}],
        # Branch 1: A[i] >= threshold → i := i + 1.
        "g@B1.1": ["A[i] >= threshold"],
        "s@B1.1": [{"i": "i + 1"}],

        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_57/lean/SynthLean/Y2Corpus/verina_basic_57",
    solver_timeout_ms = 1_800_000,   # 30 min budget for axiom-heavy
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    print(f"wall: {time.monotonic() - t:.1f}s")
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
