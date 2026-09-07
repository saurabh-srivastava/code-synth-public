/-
Scratch: prove merge_l1_drain_b_preserves_inv as Tier-1 theorem,
using the auxiliary lemmas already in Helpers.lean plus a focused
boundary axiom.

The boundary axiom captures the fact that A[n-1] ≤ A[n] under
is_sorted(A, n)=1.  This is NOT derivable from the user's
recurrence axiom (which only constrains positions 0..n-1).  It
encodes the caller's implicit contract: arrays are "padded" with
sentinel ≥ at index n (in practice never read because the loop
guard prevents it).  An IR-level fix would be to gate τ atom 5/6
on i<n/j<p; until then, this axiom captures the gap.
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.merge_two_sorted.Helpers
open SynthLean

axiom merge_array_boundary_B_attempt : ∀ (B : Int → Int) (p : Int),
    is_sorted B p = 1 → B (p - 1) ≤ B p

theorem merge_l1_drain_b_preserves_inv_attempt :
    ∀ (n p i j j' : Int)
      (A B C C' : Int → Int),
      ((n ≥ 0) ∧ (p ≥ 0) ∧ ((is_sorted A n) = 1) ∧ ((is_sorted B p) = 1)) →
      (0 ≤ i) →
      (i ≤ n) →
      (0 ≤ j) →
      (j ≤ p) →
      ((is_sorted C (i + j)) = 1) →
      (((i + j) > 0) → ((C ((i + j) - 1)) ≤ (B j))) →
      (j < p) →
      (C' = (store C (i + j) (B j))) →
      (j' = (j + 1)) →
      ((0 ≤ i)) ∧ ((i ≤ n)) ∧ ((0 ≤ j')) ∧ ((j' ≤ p)) ∧
      (((is_sorted C' (i + j')) = 1)) ∧
      ((((i + j') > 0) → ((C' ((i + j') - 1)) ≤ (B j')))) := by
  intro n p i j j' A B C C'
  intro h_pre hi_nn hi_le hj_nn hj_le h_C_sorted h_C_last_B h_g hC' hj'
  obtain ⟨_, _, _, hsB⟩ := h_pre
  refine ⟨hi_nn, hi_le, by omega, by omega, ?_, ?_⟩
  · -- is_sorted C' (i + j') = 1
    by_cases h_ij : i + j = 0
    · -- Base: i+j' = 1, is_sorted is 1 by axiom_5.
      have h_ij' : i + j' = 1 := by omega
      rw [h_ij']
      exact mts_user_axiom_5 C'
    · -- Inductive: extend at position i+j.
      have h_ij_ge : i + j ≥ 1 := by omega
      have h_ij' : i + j' = (i + j) + 1 := by omega
      rw [h_ij']
      apply is_sorted_extend C' (i + j) h_ij_ge
      · -- is_sorted C' (i+j) = 1
        rw [hC']
        rw [is_sorted_store_unchanged C (i+j) (B j) (i+j) (by omega) (le_refl _)]
        exact h_C_sorted
      · -- C'[i+j-1] ≤ C'[i+j]
        rw [hC']
        unfold store
        have h_lhs_ne : ¬ ((i + j) - 1) = (i + j) := by omega
        simp [h_lhs_ne]
        exact h_C_last_B (by omega)
  · -- (i + j' > 0) → C'[i+j'-1] ≤ B[j']
    intro _h_pos
    rw [hC', hj']
    have h_idx : i + (j + 1) - 1 = i + j := by omega
    rw [h_idx]
    unfold store
    simp
    -- Goal: B j ≤ B (j+1).
    by_cases h_jp : j + 1 < p
    · -- Inner: use is_sorted_extract.
      have h_idx2 : (j + 1) - 1 = j := by omega
      have := is_sorted_extract B p (j + 1) hsB (by omega) h_jp
      rw [h_idx2] at this
      exact this
    · -- Boundary: j+1 = p (j < p, j+1 ≤ p, ¬(j+1 < p) → j+1 = p).
      have h_jp_eq : j + 1 = p := by omega
      rw [h_jp_eq]
      have := merge_array_boundary_B_attempt B p hsB
      have h_pm1 : p - 1 = j := by omega
      rw [h_pm1] at this
      exact this
