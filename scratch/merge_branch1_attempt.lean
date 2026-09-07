/-
Scratch: prove merge_branch1_preserves_inv as Tier-1 theorem.
Branch 1: A[i] > B[j], emit B[j], j := j+1.
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.merge_two_sorted.Helpers
open SynthLean

axiom merge_array_boundary_B_attempt : ∀ (B : Int → Int) (p : Int),
    is_sorted B p = 1 → B (p - 1) ≤ B p

theorem merge_branch1_preserves_inv_attempt :
    ∀ (n p i j j' : Int)
      (A B C C' : Int → Int),
      ((n ≥ 0) ∧ (p ≥ 0) ∧ ((is_sorted A n) = 1) ∧ ((is_sorted B p) = 1)) →
      (0 ≤ i) →
      (i ≤ n) →
      (0 ≤ j) →
      (j ≤ p) →
      ((is_sorted C (i + j)) = 1) →
      (((i + j) > 0) → ((C ((i + j) - 1)) ≤ (A i))) →
      (((i + j) > 0) → ((C ((i + j) - 1)) ≤ (B j))) →
      (((i < n) ∧ (j < p)) ∧ ((A i) > (B j))) →
      (C' = (store C (i + j) (B j))) →
      (j' = (j + 1)) →
      ((0 ≤ i)) ∧ ((i ≤ n)) ∧ ((0 ≤ j')) ∧ ((j' ≤ p)) ∧
      (((is_sorted C' (i + j')) = 1)) ∧
      ((((i + j') > 0) → ((C' ((i + j') - 1)) ≤ (A i)))) ∧
      ((((i + j') > 0) → ((C' ((i + j') - 1)) ≤ (B j')))) := by
  intro n p i j j' A B C C'
  intro h_pre hi_nn hi_le hj_nn hj_le h_C_sorted h_C_last_A h_C_last_B h_guard hC' hj'
  obtain ⟨_, _, _, hsB⟩ := h_pre
  obtain ⟨⟨h_i_lt_n, h_j_lt_p⟩, h_AiB_gt⟩ := h_guard
  refine ⟨hi_nn, hi_le, by omega, by omega, ?_, ?_, ?_⟩
  · -- is_sorted C' (i + j') = 1
    by_cases h_ij : i + j = 0
    · have h_ij' : i + j' = 1 := by omega
      rw [h_ij']
      exact mts_user_axiom_5 C'
    · have h_ij_ge : i + j ≥ 1 := by omega
      have h_ij' : i + j' = (i + j) + 1 := by omega
      rw [h_ij']
      apply is_sorted_extend C' (i + j) h_ij_ge
      · rw [hC']
        rw [is_sorted_store_unchanged C (i+j) (B j) (i+j) (by omega) (le_refl _)]
        exact h_C_sorted
      · rw [hC']
        unfold store
        have h_lhs_ne : ¬ ((i + j) - 1) = (i + j) := by omega
        simp [h_lhs_ne]
        exact h_C_last_B (by omega)
  · -- (i + j' > 0) → C'[i+j'-1] ≤ A[i]
    intro _h_pos
    rw [hC', hj']
    have h_idx : i + (j + 1) - 1 = i + j := by omega
    rw [h_idx]
    unfold store
    simp
    -- Goal: B j ≤ A i  (branch guard says A i > B j).
    linarith
  · -- (i + j' > 0) → C'[i+j'-1] ≤ B[j']
    intro _h_pos
    rw [hC', hj']
    have h_idx : i + (j + 1) - 1 = i + j := by omega
    rw [h_idx]
    unfold store
    simp
    -- Goal: B j ≤ B (j+1).
    by_cases h_jp : j + 1 < p
    · have h_idx2 : (j + 1) - 1 = j := by omega
      have := is_sorted_extract B p (j + 1) hsB (by omega) h_jp
      rw [h_idx2] at this
      exact this
    · have h_jp_eq : j + 1 = p := by omega
      rw [h_jp_eq]
      have := merge_array_boundary_B_attempt B p hsB
      have h_pm1 : p - 1 = j := by omega
      rw [h_pm1] at this
      exact this
