"""verina_basic_74 — maxArray (VERINA-basic port).

Return the maximum element of a non-empty integer array.

VERINA source of truth
-----------------------
Signature: `maxArray (a : Array Int) : Int`, shape array->scalar.

  precond (VERINA):
      a.size > 0

  code (VERINA): a tail-recursive scan `maxArray_aux a 1 a[0]!`
      starting at index 1 with `current = a[0]`, updating
          new_current = if current > a[index]! then current else a[index]!
      i.e. the running maximum over a[0..index).

  postcond (VERINA):
      (∀ (k : Nat), k < a.size → result >= a[k]!)      -- upper bound
    ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)        -- witness

Fidelity mapping
----------------
The VERINA postcond is a *pure first-order* upper-bound-plus-witness
predicate: `result` dominates every element AND equals some element.
No auxiliary fold/count is referenced (unlike differenceMinMax), so
this needs NO uninterpreted function and NO axioms — it is the
canonical min/max/witness shape handled by pure Z3 with quantified τ
atoms (cf. `benchmarks/array_max_val.py`, `benchmarks/max_array.py`).

Direct transcription:

    VERINA  `∀ k < a.size, result >= a[k]!`
      -> our `ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= result))`
    VERINA  `∃ k < a.size, result = a[k]!`
      -> our `Exists(lambda k: 0 <= k and k < n and A[k] == result)`

`a : Array Int` -> our `A : int[]` plus a length `n : int` with the
precondition `n >= 1` capturing `a.size > 0` (Nat-size, non-empty).
Result type Int -> our `result : int` output.  The `0 <= k` guards are
implicit in VERINA's `k : Nat`; we make them explicit for our int `k`.

Synthesized shape
-----------------
    result, i := A[0], 1
    while i < n:
        if A[i] > result:  result, i := A[i], i + 1
        else            :  i := i + 1
    return result

Loop invariant τ@L0: (∀k<i. A[k] <= result) ∧ (∃k<i. A[k] == result)
∧ 1 <= i <= n.  Pure Z3 — no Lean dispatch; the running-max invariant
is directly inductive under the two-branch body.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-empty integer array A of length n (n >= 1), "
        "return the maximum value among A[0], A[1], ..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "n >= 1",
    post     = (
        "ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= result)) and "
        "Exists(lambda k: 0 <= k and k < n and A[k] == result)"
    ),

    atoms = {
        # Init from A[0].
        "s@B0": [{"result": "A[0]", "i": "1"}],

        "tau@L0": [
            "1 <= i",
            "i <= n",
            "n >= 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] <= result))"),
            ("Exists(lambda k: 0 <= k and k < i and A[k] == result)"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] > result -> result := A[i].
        "g@B1.0": ["A[i] > result"],
        "s@B1.0": [{"result": "A[i]", "i": "i + 1"}],
        # Branch 1: A[i] <= result -> no change.
        "g@B1.1": ["A[i] <= result"],
        "s@B1.1": [{"i": "i + 1"}],
    },

    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,
    wedge_threshold = 200,

    dump_lean_failures_dir = "benchmarks/verina/verina_basic_74/lean/SynthLean/Y2Corpus/verina_basic_74",
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
