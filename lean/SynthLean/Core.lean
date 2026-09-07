/-
SynthLean.Core — minimal definitions used by the synthesizer's
emitted theorems, WITHOUT a mathlib dependency.

Splitting this out from `SynthLean.Basic` is a performance
optimization: `Mathlib.Tactic` import adds ~3s per `lake env
lean` invocation (mathlib olean preload).  For trivial proofs
that close via `omega` / `subst_eqs` / direct citation only,
importing Core alone keeps per-dispatch latency to ~1.4s
instead of ~4.5s.

Any theorem that needs `linarith`, `nlinarith`, `ring`,
`aesop`, `simp_all` with mathlib lemmas, etc. must import
`SynthLean.Basic` (which re-exports Core + mathlib).
-/

namespace SynthLean

/-- Array Store: `(store A i v) k = if k = i then v else A k`.
    Indices are `Int` to match the program's integer loop
    counters without coercions; user-authored `0 ≤ k`
    invariants then carry actual content rather than being
    trivially true (which they would be under `Nat`). -/
def store (A : Int → Int) (i : Int) (v : Int) : Int → Int :=
  fun k => if k = i then v else A k

/-- 2D array Store for `int[][]` benchmarks (matrix_init, lcs,
    grid_paths).  Updates cell (i, j) of `A : Int → Int → Int`
    to `v`. -/
def store2d (A : Int → Int → Int) (i j : Int) (v : Int) :
    Int → Int → Int :=
  fun p q => if p = i ∧ q = j then v else A p q

end SynthLean
