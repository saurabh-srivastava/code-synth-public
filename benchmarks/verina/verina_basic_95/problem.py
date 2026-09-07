"""verina_basic_95 — swap (ported from VERINA).

Source: /private/tmp/verina-data/datasets/verina/verina_basic_95/
Upstream: Clover task_id `Clover_swap_in_array`.

VERINA signature (source of truth):
    swap(arr : Array Int, i : Int, j : Int) -> Array Int

VERINA precondition (task.lean, between @start/@end precond):
    i ≥ 0 ∧
    j ≥ 0 ∧
    Int.toNat i < arr.size ∧
    Int.toNat j < arr.size

VERINA reference code (between @start/@end code):
    let i_nat := Int.toNat i
    let j_nat := Int.toNat j
    let arr1 := arr.set! i_nat (arr[j_nat]!)   -- reads ORIGINAL arr[j]
    let arr2 := arr1.set! j_nat (arr[i_nat]!)  -- reads ORIGINAL arr[i]
    arr2

VERINA postcondition (between @start/@end postcond, 4 conjuncts):
    result.size = arr.size ∧
    result[Int.toNat i]! = arr[Int.toNat j]! ∧
    result[Int.toNat j]! = arr[Int.toNat i]! ∧
    (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j →
        result[k]! = arr[k]!)

Mapping to this framework
-------------------------
This is the arbitrary-index sibling of verina_basic_32
(swap_first_last); it is the same shape as benchmarks/array_swap.py.

Nat/Int handling: VERINA's i, j are Int constrained non-negative by
the precond (i ≥ 0 ∧ j ≥ 0) and converted with Int.toNat; we model
them as `int` with the explicit `0 <= i` / `0 <= j` guards, so
Int.toNat i / Int.toNat j collapse to i / j exactly.  n := arr.size.

The synthesizer models arrays as unbounded Z3 maps with a separate
length variable `n`; there is no reified `.size`, so conjunct 1
(`result.size = arr.size`) is preserved automatically by in-place
Update and needs no explicit atom.  The remaining three conjuncts
map directly.  Because the output overwrites A, we thread a ghost
copy `B` of the original array (caller passes A twice; Pre pins
B == A on [0, n)) so the post can refer to the *original* values —
the standard "old_A" trick (see benchmarks/array_swap.py).

The i == j case is admitted by VERINA (precond does not require
i ≠ j) and is handled here: with i == j the nested Update reduces to
A[i] := A[i] (a no-op on the touched cell), and both index conjuncts
degenerate to A[i] == B[i], which holds since Pre pins B == A.

Fidelity: EXACT.  Conjunct 1 is structural (Update preserves size);
conjuncts 2/3/4 map one-to-one to our post, with VERINA's Nat k over
[0, arr.size) matching our integer k over [0, n) (the Pre pins B == A
only on [0, n), so k is constrained to that range).

Spec:
    Pre  : 0 <= i < n ∧ 0 <= j < n ∧ (∀k. 0 <= k < n ⇒ B[k] == A[k])
    Post : A[i] == B[j] ∧ A[j] == B[i] ∧
           (∀k. 0 <= k < n ∧ k != i ∧ k != j ⇒ A[k] == B[k])

Straight-line SB, one nested Update, pure Z3 (no UF, no Lean).
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n and indices i, j "
        "(both valid for A), exchange the values at positions i "
        "and j in A.  All other positions are unchanged."
    ),

    template = SB(n=1),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),   # ghost copy of the original A
                Var("i", "int", "input"),
                Var("j", "int", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = ("(0 <= i) and (i < n) and (0 <= j) and (j < n) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    # conjunct 2: result[i] == a[j]
    # conjunct 3: result[j] == a[i]
    # conjunct 4: every other in-range index unchanged
    post     = ("(A[i] == B[j]) and (A[j] == B[i]) and "
                "ForAll(lambda k: Implies("
                "0 <= k and k < n and k != i and k != j, A[k] == B[k]))"),
    atoms = {
        # Nested Update: swap A[i] and A[j].  The RHS reads the
        # ORIGINAL A (pre-state), so no temporary is needed.
        "s@B0": [
            {"A": "Update(Update(A, i, A[j]), j, A[i])"},
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_95/lean/SynthLean/Y2Corpus/verina_basic_95",
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
