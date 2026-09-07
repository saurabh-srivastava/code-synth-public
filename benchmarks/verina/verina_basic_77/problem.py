"""verina_basic_77 — modify_array_element (2D array point-write).

Port of VERINA-basic task `verina_basic_77` (upstream Clover
`Clover_modify_2d_array`).  Given a 2-D array `arr` and indices
`index1`, `index2` plus a value `val`, set `arr[index1][index2] :=
val`, leaving every other cell (and every other inner array)
unchanged.

VERINA source of truth
----------------------
Signature (task.json):
    arr    : Array (Array Nat)
    index1 : Nat
    index2 : Nat
    val    : Nat
    result : Array (Array Nat)

precond (task.lean):
    index1 < arr.size ∧
    index2 < (arr[index1]!).size

reference code (task.lean):
    let inner  := arr[index1]!
    let inner' := inner.set! index2 val        -- updateInner
    arr.set! index1 inner'

postcond (task.lean):
    result.size = arr.size ∧
    (result[index1]!).size = (arr[index1]!).size ∧
    (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
    (∀ j, j < (arr[index1]!).size → j ≠ index2
              → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
    ((result[index1]!)[index2]! = val)

Modelling / fidelity notes
--------------------------
- `Array (Array Nat)`  →  our native `int[][]` sort
  (`Array Int (Array Int Int)`).  `arr[i][j]` is
  `Select(Select(arr,i),j)`; the point-write
  `arr[index1][index2] := val` is `Update(A, index1, index2, val)`
  (= `Store(A, index1, Store(Select(A,index1), index2, val))`).
- Nat → int with the implied non-negativity constraints
  (`index1 >= 0`, `index2 >= 0`, `val >= 0`) added to the pre.
- SMT arrays are *total functions* with no intrinsic `.size`, so
  the two `.size = .size` postcond conjuncts (outer + inner-at-
  index1) are NOT representable and are dropped.  They hold
  trivially of `set!` in Lean (a store never resizes).  We instead
  carry the sizes as explicit ints `m` (= arr.size) and `w`
  (= (arr[index1]).size) purely to BOUND the two universally-
  quantified conjuncts exactly as VERINA does (`i < arr.size`,
  `j < (arr[index1]).size`).
- The postcond references the ORIGINAL `arr`, but our output array
  is mutated in place, so — following the `array_swap` /
  `swap_first_last` convention — we pass a ghost copy `B` of the
  original and pin `A == B` in the pre.  `B` is never written, so
  in the post it still denotes the original 2-D array.
- Conjunct 3 (`result[i]! = arr[i]!`, whole-inner-array equality)
  is modelled as Z3 extensional array equality `A[i] == B[i]`
  (`A[i]` is a row of sort `Array Int Int`) — the faithful analogue
  of Lean array-value equality, and it needs no per-row size bound.

Faithfulness: the two dropped `.size` conjuncts are the only gap;
every semantic conjunct (untouched rows, untouched cells in the
target row, and the single updated cell) is captured exactly.

Pure Z3 (single acyclic transition, no UF, no Lean dispatch).
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given a 2-D integer array A, a ghost copy B of the original "
        "A, indices index1 (valid outer, < m) and index2 (valid inner, "
        "< w), and a value val, set A[index1][index2] := val.  Every "
        "other inner array and every other cell of the target row are "
        "unchanged."
    ),

    template = SB(n=1),
    # B is the ghost copy of the ORIGINAL 2-D array (caller passes A twice).
    inputs   = [Var("A", "int[][]", "input"),
                Var("B", "int[][]", "input"),
                Var("index1", "int", "input"),
                Var("index2", "int", "input"),
                Var("val", "int", "input"),
                Var("m", "int", "input"),   # outer size  = arr.size
                Var("w", "int", "input")],  # inner size   = (arr[index1]).size
    outputs  = [Var("A", "int[][]", "output")],

    # Nat params → int with implied >= 0.  VERINA precond:
    #   index1 < arr.size  →  index1 < m   (with index1 >= 0)
    #   index2 < (arr[index1]).size  →  index2 < w   (with index2 >= 0)
    pre      = ("(A == B) and "
                "(0 <= index1) and (index1 < m) and "
                "(0 <= index2) and (index2 < w) and "
                "(0 <= val)"),

    post     = (
        # (3) every inner array besides index1 is unchanged
        "ForAll(lambda i: Implies("
        "0 <= i and i < m and i != index1, A[i] == B[i])) and "
        # (4) in the target row, every cell besides index2 is unchanged
        "ForAll(lambda j: Implies("
        "0 <= j and j < w and j != index2, "
        "A[index1][j] == B[index1][j])) and "
        # (5) the single updated cell now holds val
        "(A[index1][index2] == val)"
    ),

    atoms = {
        # Single transition: 2-D point-write at (index1, index2).
        "s@B0": [
            {"A": "Update(A, index1, index2, val)"},
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/verina_basic_77_modify_array_element"),
    wedge_threshold = 200,
    solver_timeout_ms = 60_000,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    elapsed = time.monotonic() - t
    print(f"wall: {elapsed:.1f}s")
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
