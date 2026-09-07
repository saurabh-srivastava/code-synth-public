/-
Scratch: prove merge_l2_drain_a_preserves_inv as Tier-1 theorem.
Mirror of drain_b (swap A↔B, i↔j).
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.merge_two_sorted.Helpers
open SynthLean

axiom merge_array_boundary_A_attempt : ∀ (A : Int → Int) (n : Int),
    is_sorted A n = 1 → A (n - 1) ≤ A n

theorem merge_l2_drain_a_preserves_inv_attempt :
    ∀ (n p i j i' : Int)
      (A B C C' : Int → Int),
      ((n ≥ 0) ∧ (p ≥ 0) ∧ ((is_sorted A n) = 1) ∧ ((is_sorted B p) = 1)) →
      (0 ≤ i) →
      (i ≤ n) →
      (0 ≤ j) →
      (j ≤ p) →
      ((is_sorted C (i + j)) = 1) →
      (((i + j) > 0) → ((C ((i + j) - 1)) ≤ (A i))) →
      (i < n) →
      (C' = (store C (i + j) (A i))) →
      (i' = (i + 1)) →
      ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((0 ≤ j)) ∧ ((j ≤ p)) ∧
      (((is_sorted C' (i' + j)) = 1)) ∧
      ((((i' + j) > 0) → ((C' ((i' + j) - 1)) ≤ (A i')))) := by
  intro n p i j i' A B C C'
  intro h_pre hi_nn hi_le hj_nn hj_le h_C_sorted h_C_last_A h_g hC' hi'
  obtain ⟨_, _, hsA, _⟩ := h_pre
  refine ⟨by omega, by omega, hj_nn, hj_le, ?_, ?_⟩
  · -- is_sorted C' (i' + j) = 1
    by_cases h_ij : i + j = 0
    · have h_ij' : i' + j = 1 := by omega
      rw [h_ij']
      exact mts_user_axiom_5 C'
    · have h_ij_ge : i + j ≥ 1 := by omega
      have h_ij' : i' + j = (i + j) + 1 := by omega
      rw [h_ij']
      apply is_sorted_extend C' (i + j) h_ij_ge
      · rw [hC']
        rw [is_sorted_store_unchanged C (i+j) (A i) (i+j) (by omega) (le_refl _)]
        exact h_C_sorted
      · rw [hC']
        unfold store
        have h_lhs_ne : ¬ ((i + j) - 1) = (i + j) := by omega
        simp [h_lhs_ne]
        exact h_C_last_A (by omega)
  · -- (i' + j > 0) → C'[i'+j-1] ≤ A[i']
    intro _h_pos
    rw [hC', hi']
    have h_idx : (i + 1) + j - 1 = i + j := by omega
    rw [h_idx]
    unfold store
    simp
    -- Goal: A i ≤ A (i+1).
    by_cases h_in : i + 1 < n
    · have h_idx2 : (i + 1) - 1 = i := by omega
      have := is_sorted_extract A n (i + 1) hsA (by omega) h_in
      rw [h_idx2] at this
      exact this
    · -- Boundary: i+1 = n.
      have h_in_eq : i + 1 = n := by omega
      rw [h_in_eq]
      have := merge_array_boundary_A_attempt A n hsA
      have h_nm1 : n - 1 = i := by omega
      rw [h_nm1] at this
      exact this
