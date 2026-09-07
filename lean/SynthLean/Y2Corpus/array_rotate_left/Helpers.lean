/-
array_rotate_left Tier-3 helper.

One helper covers the chain-bundle-post obligation for the
single Loop in `SB() >> Loop(SB()) >> SB()`:

  arl_post : pre ∧ τ_loop ∧ ¬g ∧ h_skip ∧ h_init ⇒ post

The proof uses:
  - h_not_g + h_tau_1 + h_tau_2 ⇒ i' = n - 1
  - For 0 ≤ k < n-1: store A' (n-1) saved k = A' k (k ≠ n-1)
                    then h_tau_4 closes A' k = B (k+1)
  - For k = n-1: store A' (n-1) saved (n-1) = saved, then
                 h_tau_3 gives saved = B 0

The chain-bundle FLAT translator emits this exact signature
after the #242 fix (translate.py supports skip-rewrites of
loop-modified vars via the `<var>_post` binder).
-/
import SynthLean.Basic
open SynthLean

namespace SynthLean.Y2Corpus.ArrayRotateLeft

set_option linter.unusedVariables false in
theorem arl_post :
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
  · intros k hk
    obtain ⟨hk_lo, hk_hi⟩ := hk
    rw [h_skip_A]
    show (store A' (n-1) saved) k = B (k + 1)
    simp [store, show k ≠ n - 1 by omega]
    apply h_tau_4
    omega
  · rw [h_skip_A]
    show (store A' (n-1) saved) (n - 1) = B 0
    simp [store]
    exact h_tau_3

end SynthLean.Y2Corpus.ArrayRotateLeft
