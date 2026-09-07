import SynthLean.Basic
open SynthLean

-- Scratch proof for array_rotate_left's sc4 (chain-bundle-post).
-- Goal:
--   pre ∧ τ_loop ∧ ¬g ∧ h_skip ∧ h_init ⇒ post
-- where post = (∀k. 0≤k<n-1 → A_post k = B (k+1)) ∧ A_post(n-1) = B 0
-- and A_post = store A' (n-1) saved.
--
-- Key facts:
--   - h_tau_1 + h_not_g + h_tau_2 forces i' = n-1.
--   - For 0 ≤ k < n-1 = i': store A' (n-1) saved k = A' k (k ≠ n-1), then h_tau_4.
--   - For k = n-1: store A' (n-1) saved (n-1) = saved, and h_tau_3 gives saved = B 0.

set_option linter.unusedVariables false in
theorem array_rotate_left_post :
    ∀ (n saved i : Int) (A B : Int → Int) (i' : Int)
      (A' A_post : Int → Int),
    (n ≥ 1 ∧ (∀ (k : Int), (0 ≤ k ∧ k < n) → B k = A k)) →
    0 ≤ i' → i' ≤ n - 1 → n ≥ 1 →
    saved = B 0 →
    (∀ (k : Int), (0 ≤ k ∧ k < i') → A' k = B (k + 1)) →
    (∀ (k : Int), (i' ≤ k ∧ k < n) → A' k = B k) →
    ¬ (i' < n - 1) →
    A_post = store A' (n - 1) saved →
    saved = A 0 →
    (∀ (k : Int), (0 ≤ k ∧ k < n - 1) → A_post k = B (k + 1)) ∧
    A_post (n - 1) = B 0 := by
  intros n saved i A B i' A' A_post h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3
         h_tau_4 h_tau_5 h_not_g h_skip_A h_init_saved
  have h_i_eq : i' = n - 1 := by omega
  refine ⟨?_, ?_⟩
  · -- ∀ k. 0 ≤ k < n-1 → A_post k = B (k+1)
    intros k hk
    obtain ⟨hk_lo, hk_hi⟩ := hk
    rw [h_skip_A]
    -- (store A' (n-1) saved) k = A' k  since k < n-1 so k ≠ n-1
    show (store A' (n-1) saved) k = B (k + 1)
    simp [store, show k ≠ n - 1 by omega]
    -- Now goal: A' k = B (k+1).  Use h_tau_4 with bounds 0 ≤ k < i' = n-1.
    apply h_tau_4
    omega
  · -- A_post (n-1) = B 0
    rw [h_skip_A]
    show (store A' (n-1) saved) (n - 1) = B 0
    simp [store]
    exact h_tau_3
