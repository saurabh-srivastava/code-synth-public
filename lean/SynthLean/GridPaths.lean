/-
SynthLean.GridPaths — Day 5: hand-written grid_paths inner inductive.

`benchmarks/grid_paths.py` wedges the SMT path past 10 minutes
(documented in CLAUDE.md / research.claude.md as a known-timeout
research data point).  The bottleneck is the inductive validity
check on the inner loop's τ — Z3 can't dispatch quantified
invariants over 2D arrays composed with a UF recurrence axiom in
reasonable time.

This file proves the same obligation in Lean 4 with mathlib.
The proof is **hand-written** for now; Day 6+ generalizes the
translator to emit this structurally.

The obligation: for each inner-loop iteration, the chosen
invariant τ_inner is preserved across the transition

    L  := store2d L i j (L (i-1) j + L i (j-1))
    j  := j + 1

assuming `paths` is the standard lattice-paths function with
the recurrence `paths(i, j) = paths(i-1, j) + paths(i, j-1)`
for i, j ≥ 1, and base values `paths(0, _) = paths(_, 0) = 1`.

If this proves, Ring 1's capability claim is validated: Lean
dispatches an obligation the SMT path can't.
-/
import SynthLean.Basic
import Mathlib.Tactic
open SynthLean

namespace SynthLean.GridPaths

/-- The `paths` function lives at the spec level — uninterpreted to
    the program but with a recurrence supplied as axioms.  We
    declare it as an `axiom` (its existence + type, not a
    definition); the recurrence/base axioms below relate it.

    Translator-emission Day-6 work: emit these alongside the
    theorem from `Problem.uninterpreted` + `Problem.axioms`. -/
axiom paths : Int → Int → Int

/-- Base case: row 0 is all 1s.  Mirrors `Problem.axioms[0]`. -/
axiom paths_base_row : ∀ j : Int, j ≥ 0 → paths 0 j = 1

/-- Base case: column 0 is all 1s.  Mirrors `Problem.axioms[1]`. -/
axiom paths_base_col : ∀ i : Int, i ≥ 0 → paths i 0 = 1

/-- Recurrence.  Mirrors `Problem.axioms[2]`. -/
axiom paths_rec : ∀ i j : Int, i ≥ 1 → j ≥ 1 →
    paths i j = paths (i - 1) j + paths i (j - 1)

set_option linter.unusedVariables false

/-- The inner-loop inductive obligation for grid_paths.

    τ_inner has 9 atoms; the conclusion is the same 9 with `L`,
    `j` primed.  Each `h_tau_<k>` is one chosen τ atom.

    Hypotheses (in user-authored order):
      0–5: bookkeeping (`1 ≤ i`, `i ≤ m`, `1 ≤ j`, `j ≤ n+1`,
           `m ≥ 0`, `n ≥ 0`).
      6:   rows < i fully filled with `paths`.
      7:   current row up to column `j` filled with `paths`.
      8:   column 0 across all rows is 1.

    Transition:
      `L' = store2d L i j (L (i-1) j + L i (j-1))`
      `j' = j + 1`

    The proof's structure mirrors the synthesizer's reasoning —
    each conjunct of τ_post discharged by `omega`, application of
    the corresponding pre-state hypothesis, or case analysis on
    `q = j` (the position just updated) when the conjunct
    quantifies over array indices touched by the Update.
-/
theorem grid_paths_inner_inductive
    (m n i j : Int)
    (L : Int → Int → Int)
    (j' : Int)
    (L' : Int → Int → Int)
    -- Pre.
    (h_pre_m : m ≥ 0)
    (h_pre_n : n ≥ 0)
    -- τ_inner.
    (h_tau_0 : 1 ≤ i)
    (h_tau_1 : i ≤ m)
    (h_tau_2 : 1 ≤ j)
    (h_tau_3 : j ≤ n + 1)
    (h_tau_4 : m ≥ 0)
    (h_tau_5 : n ≥ 0)
    (h_tau_6 : ∀ p q : Int,
        (0 ≤ p ∧ p < i ∧ 0 ≤ q ∧ q ≤ n) → L p q = paths p q)
    (h_tau_7 : ∀ q : Int,
        (0 ≤ q ∧ q < j) → L i q = paths i q)
    (h_tau_8 : ∀ p : Int,
        (0 ≤ p ∧ p ≤ m) → L p 0 = 1)
    -- Loop guard (negation handled at the chain bundle level; the
    -- inductive sees the positive form).
    (h_guard : j ≤ n)
    -- Transition.
    (h_trans_L : L' = store2d L i j (L (i - 1) j + L i (j - 1)))
    (h_trans_j : j' = j + 1) :
    -- Post-state τ_inner — same 9 conjuncts, L, j primed.
    (1 ≤ i) ∧
    (i ≤ m) ∧
    (1 ≤ j') ∧
    (j' ≤ n + 1) ∧
    (m ≥ 0) ∧
    (n ≥ 0) ∧
    (∀ p q : Int,
        (0 ≤ p ∧ p < i ∧ 0 ≤ q ∧ q ≤ n) → L' p q = paths p q) ∧
    (∀ q : Int,
        (0 ≤ q ∧ q < j') → L' i q = paths i q) ∧
    (∀ p : Int,
        (0 ≤ p ∧ p ≤ m) → L' p 0 = 1) := by
  subst h_trans_L h_trans_j
  refine ⟨h_tau_0, h_tau_1, ?_, ?_, h_tau_4, h_tau_5, ?_, ?_, ?_⟩
  · -- 1 ≤ j + 1, from h_tau_2.
    omega
  · -- j + 1 ≤ n + 1, from h_guard.
    omega
  · -- ∀ p q. (p < i) ∧ ... → store2d L i j _ p q = paths p q
    intro p q ⟨hp_lo, hp_hi, hq_lo, hq_hi⟩
    have h_ne : ¬ (p = i ∧ q = j) := fun ⟨hpi, _⟩ => by omega
    simp [store2d, h_ne]
    exact h_tau_6 p q ⟨hp_lo, hp_hi, hq_lo, hq_hi⟩
  · -- ∀ q. (q < j + 1) → store2d L i j _ i q = paths i q
    intro q ⟨hq_lo, hq_hi⟩
    unfold store2d
    by_cases hqj : q = j
    · -- q = j: the just-updated cell.  Result is the RHS of Update.
      rw [if_pos ⟨rfl, hqj⟩]
      have h_ij  : L (i - 1) j = paths (i - 1) j :=
        h_tau_6 (i - 1) j ⟨by omega, by omega, by omega, by omega⟩
      have h_iq1 : L i (j - 1) = paths i (j - 1) :=
        h_tau_7 (j - 1) ⟨by omega, by omega⟩
      rw [hqj, h_ij, h_iq1]
      -- paths (i-1) j + paths i (j-1) = paths i j  by paths_rec.
      exact (paths_rec i j h_tau_0 h_tau_2).symm
    · -- q ≠ j: untouched.  store2d evaluates to L i q.
      rw [if_neg (fun ⟨_, hqj'⟩ => hqj hqj')]
      exact h_tau_7 q ⟨hq_lo, by omega⟩
  · -- ∀ p. (p ≤ m) → store2d L i j _ p 0 = 1
    intro p ⟨hp_lo, hp_hi⟩
    have h_ne : ¬ (p = i ∧ (0 : Int) = j) := fun ⟨_, h0j⟩ => by omega
    simp [store2d, h_ne]
    exact h_tau_8 p ⟨hp_lo, hp_hi⟩

end SynthLean.GridPaths
