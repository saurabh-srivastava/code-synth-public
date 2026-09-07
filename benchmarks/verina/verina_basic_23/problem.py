"""verina_basic_23 — differenceMinMax (VERINA-basic port).

Return the difference between the largest and the smallest value
in a non-empty integer array.

VERINA source of truth
-----------------------
Signature: `differenceMinMax (a : Array Int) : Int`, shape
array->scalar.

  precond (VERINA):
      a.size > 0

  code (VERINA): a tail-recursive scan starting at index 1 with
      minVal = maxVal = a[0], updating
          newMin = if x < minVal then x else minVal
          newMax = if x > maxVal then x else maxVal
      and returning `maxVal - minVal`.

  postcond (VERINA):
      result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!))
             = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))

  i.e. `result = (max fold) - (min fold)`.

Fidelity mapping
----------------
The VERINA postcond references TWO `a.foldl` reductions over the
whole array, each seeded with `a[0]`.  Per the repo convention
(fold/count/sum/product -> UF + recurrence axioms, cf.
`benchmarks/sum_array.py`, `benchmarks/count_zeros.py`), each fold
is modelled as an uninterpreted function with a base case + a
step recurrence that *literally transcribes* the Lean fold's
lambda body:

    arrmin(A, 0)     = A[0]                                   -- seed acc = a[0]
    arrmin(A, k + 1) = (A[k] if A[k] < arrmin(A, k) else arrmin(A, k))
    arrmax(A, 0)     = A[0]
    arrmax(A, k + 1) = (A[k] if A[k] > arrmax(A, k) else arrmax(A, k))

`arrmin(A, n)` is exactly `a.foldl (fun acc x => if x < acc then x
else acc) (a[0]!)` (fold seeded with a[0], processing a[0..n));
note that processing a[0] against seed a[0] is idempotent, so
seeding-at-a[0]-then-folding-from-0 equals VERINA's
seed-at-a[0]-then-loop-from-1.  Likewise for `arrmax`.

Our post is the verbatim VERINA relation over these UFs:

    result + arrmin(A, n) == arrmax(A, n)

`a : Array Int` -> our `A : int[]` plus a length `n : int` with the
precondition `n >= 1` capturing `a.size > 0` (Nat-size, non-empty).
Result type Int -> our `result : int` output.

Synthesized shape
-----------------
    minVal, maxVal, i := A[0], A[0], 0
    while i < n:
        minVal := A[i] if A[i] < minVal else minVal
        maxVal := A[i] if A[i] > maxVal else maxVal
        i := i + 1
    result := maxVal - minVal

Loop invariant τ@L0: minVal == arrmin(A, i) ∧ maxVal == arrmax(A, i)
∧ 0 <= i <= n.  Like sum_array this is axiom-heavy: Z3 must apply
the recurrence axioms to discharge the inductive, so the safety /
entry-bundle / chain-bundle obligations dispatch to Lean and are
closed by curated `.solved.lean` companions under
lean/SynthLean/Y2Corpus/verina_basic_23_differenceMinMax/.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-empty integer array A of length n (n >= 1), "
        "return the difference between the largest and the smallest "
        "value among A[0], A[1], ..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=1)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("minVal", "int", "local"),
                Var("maxVal", "int", "local"),
                Var("i", "int", "local")],

    uninterpreted = [
        ("arrmin", ["int[]", "int"], "int"),
        ("arrmax", ["int[]", "int"], "int"),
    ],
    axioms = [
        # user_axiom_0 — arrmin base (fold seed = a[0]).
        "arrmin(A, 0) == A[0]",
        # user_axiom_1 — arrmin step (verbatim fold lambda).
        ("ForAll(lambda k: Implies(k >= 0, "
         "arrmin(A, k + 1) == (A[k] if A[k] < arrmin(A, k) else arrmin(A, k))))"),
        # user_axiom_2 — arrmax base.
        "arrmax(A, 0) == A[0]",
        # user_axiom_3 — arrmax step.
        ("ForAll(lambda k: Implies(k >= 0, "
         "arrmax(A, k + 1) == (A[k] if A[k] > arrmax(A, k) else arrmax(A, k))))"),
    ],

    pre  = "n >= 1",
    post = "result + arrmin(A, n) == arrmax(A, n)",

    atoms = {
        # Entry: minVal, maxVal, i := A[0], A[0], 0
        "s@B0": [{"minVal": "A[0]", "maxVal": "A[0]", "i": "0"}],

        "tau@L0": [
            "minVal == arrmin(A, i)",
            "maxVal == arrmax(A, i)",
            "0 <= i",
            "i <= n",
            # NOTE: `n >= 1` is intentionally NOT a τ atom.  It is a
            # pure distractor here — every obligation (entry / inductive
            # / post / ranking) derives its `n` bound from the
            # precondition `n >= 1` (h_pre) or from `i <= n` + the loop
            # guard, so carrying it in τ only inflates the 2^|τ|
            # per-constraint enumeration (esp. the ranking treadmill).
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Loop body: minVal/maxVal conditional update; i := i + 1.
        "s@B1": [{
            "minVal": "A[i] if A[i] < minVal else minVal",
            "maxVal": "A[i] if A[i] > maxVal else maxVal",
            "i":      "i + 1",
        }],

        # Exit SB: result := maxVal - minVal
        "s@B2": [{"result": "maxVal - minVal"}],
    },

    max_solutions = 1,
    expected_solutions = 1,
    # Axiom-heavy: the 3 load-bearing obligations (entry-bundle sc0,
    # loop inductive sc1, chain-bundle post sc4) dispatch to Lean and
    # close via the curated `.solved.lean` companions in this bench's
    # dump dir.  The overall `lean_dispatch.valid` count is much higher
    # (~38 observed) because ranking-lb subsets route through Lean too
    # under axiom interference; that total is Z3-nondeterministic and
    # non-portable, so this guard is informative only (None = no strict
    # regression check).
    expected_lean_hits = None,
    solver_timeout_ms = 900_000,
    wedge_threshold = 200,

    dump_lean_failures_dir = "benchmarks/verina/verina_basic_23/lean/SynthLean/Y2Corpus/verina_basic_23",
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
