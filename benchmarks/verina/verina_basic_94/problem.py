"""verina_basic_94 (iter_copy) — VERINA-basic port.

Copy an input array into a fresh array of the same size with identical
elements in the same order.  Pointwise identity copy; SMT-tractable,
NO uninterpreted functions.  Same shape as `benchmarks/array_copy.py`.

VERINA source (datasets/verina/verina_basic_94):
    signature : iter_copy (s : Array Int) : Array Int
    precond   : True   (no preconditions; empty or non-empty ok)
    code      : loop i from 0, acc.push s[i] until i = s.size
    postcond  : (s.size = result.size)
                ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)

Fidelity map (VERINA → this Problem):
    - VERINA `s : Array Int` (input)         → input array `A`.
    - VERINA `result : Array Int` (returned) → output array `B`.
    - VERINA `s.size` (a Nat)                → length param `n` with
      the implied `n >= 0` precondition.
    - VERINA postcond clause 1 `s.size = result.size` is captured BY
      CONSTRUCTION: our framework models the output array `B` over the
      fixed index range [0, n) where n = s.size, so the returned array
      has exactly the input's length.  There is no dynamic-resize
      primitive; the size-equality obligation is discharged
      structurally rather than as an SMT clause.
    - VERINA postcond clause 2 `∀ i < s.size, s[i]! = result[i]!`
      maps directly to our post
      `ForAll k. 0 <= k < n ⇒ B[k] == A[k]`.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  B[k] == A[k]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n (n >= 0), produce an "
        "array B of the same length whose elements are identical to "
        "A's in the same order: B[k] == A[k] for every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))",

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "ForAll(lambda k: Implies(0 <= k and k < i, B[k] == A[k]))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Body: B[i] := A[i]; i := i + 1
        "s@B1": [{"B": "Update(B, i, A[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_94/lean/SynthLean/Y2Corpus/verina_basic_94",
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
