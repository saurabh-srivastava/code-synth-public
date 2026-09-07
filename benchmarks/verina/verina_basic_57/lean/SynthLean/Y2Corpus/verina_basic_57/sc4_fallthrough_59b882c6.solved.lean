/-
verina_basic_57 (CountLessThan) — loop-inductive, BRANCH 1
(A[i] ≥ threshold).  Transition: i := i+1 (c unchanged).
Argument: user_axiom_2 at k = i with (i ≥ 0 ∧ A i ≥ threshold) →
count_less(A,threshold,i+1) = count_less(A,threshold,i).
-/
import SynthLean.Core
open SynthLean

axiom count_less : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (threshold : Int), ((count_less A threshold 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (threshold : Int),
  (∀ (k : Int), (((k ≥ 0) ∧ ((A k) < threshold)) →
    ((count_less A threshold (k + 1)) = ((count_less A threshold k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (threshold : Int),
  (∀ (k : Int), (((k ≥ 0) ∧ ((A k) ≥ threshold)) →
    ((count_less A threshold (k + 1)) = (count_less A threshold k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc4_fallthrough
    (n threshold c i : Int)
    (A : Int → Int)
    (i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count_less A threshold i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : ((i < n) ∧ ((A i) ≥ threshold)))
    (h_trans_i : i' = (i + 1)) :
    ((c = (count_less A threshold i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  obtain ⟨h_loop, h_branch⟩ := h_guard
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : count_less A threshold (i + 1) = count_less A threshold i :=
      user_axiom_2 A threshold i ⟨h_tau_1, h_branch⟩
    rw [h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
