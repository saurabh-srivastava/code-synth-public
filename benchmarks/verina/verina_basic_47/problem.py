"""verina_basic_47 — arraySum (VERINA-basic port).

Compute the sum of all elements of an integer array.

VERINA source of truth
(`/private/tmp/verina-data/datasets/verina/verina_basic_47/task.lean`):

    -- signature
    arraySum (a : Array Int) (h_precond : arraySum_precond a) : Int
    -- precondition
    arraySum_precond a := a.size > 0
    -- reference implementation
    a.toList.sum
    -- auxiliary (VERINA's ground-truth sum-of-prefix)
    def sumTo (a : Array Int) (n : Nat) : Int :=
      if n = 0 then 0 else sumTo a (n - 1) + a[n - 1]!
    -- postcondition
    result - sumTo a a.size = 0  ∧  result ≥ sumTo a a.size

Algorithm synthesized here (template SB ; LOOP{ SB } ; SB):

    result := 0; i := 0;
    while (i < n):
        result := result + A[i];
        i := i + 1;
    // trailing no-op SB (return result)

Spec (this Problem):
    Pre  : n >= 1            (VERINA's `a.size > 0`; n is A's length)
    Post : result == sum(A, n)

----------------------------------------------------------------------
SPEC-FIDELITY / TRUST NOTE — `sum` UF vs VERINA's `sumTo`
----------------------------------------------------------------------
Our `sum : (Int -> Int) -> Int -> Int` is a re-axiomatization of
VERINA's ground-truth `sumTo`.  The correspondence is EXACT:

    VERINA  sumTo a 0        = 0            <->  sum(A, 0)     == 0
    VERINA  sumTo a (k+1)                        (our recurrence, k >= 0)
            = sumTo a k + a[k]              <->  sum(A, k+1)   == sum(A, k) + A[k]

    (VERINA writes the step as `sumTo a n = sumTo a (n-1) + a[n-1]!`,
     i.e. for n = k+1: `sumTo a (k+1) = sumTo a k + a[k]` — identical.)

Hence `sum(A, n)` denotes exactly `sumTo a a.size`, and our post
`result == sum(A, n)` is precisely VERINA's `result = sumTo a a.size`.
VERINA states this as the two-conjunct `result - sumTo = 0 ∧
result ≥ sumTo`, which is logically equivalent to the equality
`result = sumTo` (equality implies both a zero difference and `≥`).
So our single equality post faithfully captures VERINA's postcondition.

The TRUST SURFACE is exactly the two `sum` axioms below (base +
recurrence); they are our restatement of VERINA's `sumTo`
definitional equations.  Everything downstream (loop inductive,
loop-exit → post) is proven in Lean from those two axioms — see
lean/SynthLean/Y2Corpus/verina_basic_47_array_sum/*.solved.lean.

Structurally identical to `benchmarks/array_product.py` (same
template + UF-recurrence shape); the accumulator is additive
(base 0, step `+`) rather than multiplicative.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and its length n (with n >= 1), "
        "return the sum A[0] + A[1] + ... + A[n-1] of all elements."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("i", "int", "local")],

    # `sum` re-axiomatizes VERINA's `sumTo` (see module docstring).
    uninterpreted = [("sum", ["int[]", "int"], "int")],
    axioms = [
        # sumTo a 0 = 0
        "sum(A, 0) == 0",
        # sumTo a (k+1) = sumTo a k + a[k]
        ("ForAll(lambda k: Implies(k >= 0, "
         "sum(A, k + 1) == sum(A, k) + A[k]))"),
    ],

    pre  = "n >= 1",
    post = "result == sum(A, n)",

    atoms = {
        # result, i := 0, 0
        "s@B0": [{"result": "0", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "result == sum(A, i)",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Loop body: result := result + A[i]; i := i + 1.
        "s@B1": [{"result": "result + A[i]", "i": "i + 1"}],

        # Trailing no-op SB (return result).
        "s@B2": [ {} ],
    },

    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 900_000,   # 15 min (axiom-heavy cold run)

    # SOUND mode: hand-curated `.solved.lean` companions close the
    # axiom-heavy loop-inductive + chain-bundle-post obligations.
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_47/lean/SynthLean/Y2Corpus/verina_basic_47",
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
