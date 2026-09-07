import SynthLean.Basic
open SynthLean

namespace Scratch

theorem ap_flip_preserves_mi :
    ∀ (n found u v w : Int)
      (M : Int → Int) (G : Int → Int → Int)
      (found' : Int) (M' : Int → Int),
    (n ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) → G p q = G q p) →
    (w ≤ n) → (0 ≤ v) → (v ≤ n - 1) →
    (0 ≤ u) → (u ≤ n - 1) →
    (found = 0 ∨ found = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (0 ≤ w) →    -- NEW: atom 7
    (w < n ∧ v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧
     w ≠ u ∧ w ≠ v ∧ w ≠ M v ∧ M w = -1 ∧
     G (M v) w ≥ 1 ∧ M u = -1) →
    (M' = store (store (store (store M u v) v u) (M v) w) w (M v)) →
    (found' = 1) →
    (-1 ≤ v) ∧ (v ≤ n - 1) ∧ (0 ≤ u) ∧ (u ≤ n - 1) ∧
    (found' = 0 ∨ found' = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M' k ≠ -1) → (0 ≤ M' k ∧ M' k < n)) := by
  intros n found u v w M G found' M'
         h_pre_n h_pre_mi h_pre_sym
         h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 h_tau_7
         h_guard h_trans_M h_trans_found
  obtain ⟨h_g_w, h_g_uv, h_g_Gpos, h_g_Mv, h_g_wu, h_g_wv, h_g_wMv,
          h_g_Mw, h_g_Gz, h_g_Mu⟩ := h_guard
  have h_Mv_in : 0 ≤ M v ∧ M v < n :=
    h_pre_mi v ⟨h_tau_1, by omega, h_g_Mv⟩
  refine ⟨by omega, h_tau_2, h_tau_3, h_tau_4, by omega, ?_⟩
  intros k h_k
  obtain ⟨h_k_lo, h_k_hi, h_k_ne⟩ := h_k
  rw [h_trans_M] at h_k_ne ⊢
  simp only [store] at h_k_ne ⊢
  split_ifs at h_k_ne ⊢ with h1 h2 h3 h4
  · exact h_Mv_in
  · exact ⟨h_tau_7, by omega⟩
  · exact ⟨h_tau_3, by omega⟩
  · exact ⟨h_tau_1, by omega⟩
  · exact h_pre_mi k ⟨h_k_lo, h_k_hi, h_k_ne⟩

end Scratch
