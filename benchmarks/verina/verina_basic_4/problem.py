"""verina_basic_4 — kthElement (ported from VERINA).

Source: /private/tmp/verina-data/datasets/verina/verina_basic_4/
Upstream: dafny-synthesis task_id_101.

VERINA signature:
    kthElement(arr: Array Int, k: Nat) -> Int

VERINA precondition:
    k ≥ 1 ∧ k ≤ arr.size

VERINA reference code:
    arr[k - 1]!            -- 1-based indexing

VERINA postcondition:
    arr.any (fun x => x = result ∧ x = arr[k - 1]!)

Mapping to this framework
-------------------------
The synthesizer models arrays as unbounded Z3 maps with a separate
length variable `n` (there is no reified `.size`), so VERINA's
`arr.size` maps to `n`.  VERINA's `k : Nat` maps to our `int` k with
the implied `k >= 0`; the precond's `k >= 1` is strictly stronger,
so nonnegativity is subsumed.

VERINA's postcondition
    arr.any (fun x => x = result ∧ x = arr[k - 1]!)
asserts there EXISTS an element x of arr with x = result AND
x = arr[k-1]!.  Given the precond `1 <= k <= arr.size`, the index
`k-1` is in-bounds, so `arr[k-1]!` IS an element of arr; the
existential is therefore satisfiable iff `result = arr[k-1]!`.
Hence the postcondition is logically equivalent to
    result = arr[k - 1]
which is exactly our post `r == A[k - 1]`.  This is the fidelity
claim: our (Pre, Post) captures VERINA's spec exactly, modulo the
`arr.size` -> `n` and `Nat` -> `int` (with `k >= 1 > 0`) encodings.

Straight-line SB, one array read, pure Z3 (no UF, no Lean).
Same shape as benchmarks/last_element.py.

Spec:
    Pre  : k >= 1 ∧ k <= n
    Post : r == A[k - 1]
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n and a 1-based index k "
        "with 1 <= k <= n, return the kth element A[k - 1]."
    ),

    template = SB(n=1),
    inputs   = [Var("A", "int[]", "input"),
                Var("k", "int", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    pre      = "k >= 1 and k <= n",
    post     = "r == A[k - 1]",
    atoms = {
        "s@B0": [{"r": "A[k - 1]"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_4/lean/SynthLean/Y2Corpus/verina_basic_4",
    wedge_threshold = 200,
    solver_timeout_ms = 60_000,
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
