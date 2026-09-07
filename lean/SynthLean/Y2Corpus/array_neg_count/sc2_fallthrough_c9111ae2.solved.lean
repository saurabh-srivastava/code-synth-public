/-
array_neg_count's loop-inductive, BRANCH 0 (A[i] < 0).
Apply user_axiom_1 at k=i (i ≥ 0 ∧ A i < 0).
-/
import SynthLean.Core
open SynthLean

axiom count_neg : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((count_neg A 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int),
  (∀ k : Int, (((k ≥ 0) ∧ ((A k) < 0)) →
    ((count_neg A (k + 1)) = ((count_neg A k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int),
  (∀ k : Int, (((k ≥ 0) ∧ ((A k) ≥ 0)) →
    ((count_neg A (k + 1)) = (count_neg A k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough
    (n c i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count_neg A i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : ((i < n) ∧ ((A i) < 0)))
    (h_trans_c : c' = (c + 1))
    (h_trans_i : i' = (i + 1)) :
    ((c' = (count_neg A i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  obtain ⟨h_loop, h_branch⟩ := h_guard
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : count_neg A (i + 1) = count_neg A i + 1 :=
      user_axiom_1 A i ⟨h_tau_1, h_branch⟩
    rw [h_trans_c, h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
