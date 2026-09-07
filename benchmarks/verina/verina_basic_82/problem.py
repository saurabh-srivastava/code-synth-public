"""verina_basic_82_remove_front — VERINA-basic port.

Port of VERINA task `verina_basic_82` (remove_front, upstream
Clover `Clover_remove_front`).  Produce a new array that drops
the first element of a non-empty input array — i.e. shift every
element left by one, discarding the front.

VERINA spec (source of truth, from task.lean between the
@start/@end markers):

    precond  : a.size > 0
    code     : copyFrom a 1 (mkEmpty (a.size - 1))
               -- append a[1], a[2], ..., a[size-1] into a fresh array
    postcond : a.size > 0
             ∧ result.size = a.size - 1
             ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)

Mapping VERINA → our IR (shape = array → array):

  * `a.size` (a Nat) is modeled by a separate integer input `n`.
    VERINA's `a.size > 0` (Nat ⇒ size ≥ 1) becomes `pre: n >= 1`.
  * The output array is a distinct array `B` (write target),
    following the two-array convention of `array_copy` /
    `increment_array`.  VERINA's `result.size = a.size - 1` is
    captured structurally: we fill exactly B[0 .. n-2], and the
    postcond quantifier ranges over [0, n-1) — the "size" of the
    result in our framework is the range over which B is defined,
    which is n-1, matching `result.size = a.size - 1`.
  * VERINA's `∀ i < result.size. result[i]! = a[i + 1]!` becomes
    `ForAll k. 0 <= k < n - 1 ⇒ B[k] == A[k + 1]`.
  * The `a.size > 0` conjunct of the postcond is discharged
    directly from the precondition (it is `n >= 1`, an invariant
    carried through, so it need not appear in `post`).

This is a pointwise index-shifted copy (B[k] = A[k+1]); no fold /
sum / count auxiliary appears in VERINA's postcond, so NO
uninterpreted function is needed.  Pure Z3, quantified prefix
invariant — same skeleton as `array_copy.py` with an index offset
of +1 on the source and a loop bound of n-1 instead of n.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-empty integer array A of length n (n >= 1), "
        "produce array B that drops A's first element: B[k] equals "
        "A[k + 1] for every k in [0, n - 1).  B has length n - 1."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 1",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n - 1, B[k] == A[k + 1]))",

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n - 1",
            "ForAll(lambda k: Implies(0 <= k and k < i, B[k] == A[k + 1]))",
        ],
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - 1 - i"],

        # Body: B[i] := A[i + 1]; i := i + 1.
        "s@B1": [{"B": "Update(B, i, A[i + 1])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_82/lean/SynthLean/Y2Corpus/verina_basic_82",
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
