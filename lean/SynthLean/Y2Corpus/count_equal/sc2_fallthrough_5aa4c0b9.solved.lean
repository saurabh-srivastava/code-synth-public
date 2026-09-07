/-
count_equal's loop-inductive obligation, BRANCH 0 (A[i] == t).
τ = {c = count_eq(A, i, t), 0 ≤ i, i ≤ n}.  Transition:
c := c+1, i := i+1.

Argument: user_axiom_1 at k = i with (i ≥ 0 ∧ A i = t) →
count_eq(A, i+1, t) = count_eq(A, i, t) + 1.
-/
import SynthLean.Core
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (t : Int),
  ((count_eq A 0 t) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (t : Int),
  (∀ k : Int, (((k ≥ 0) ∧ ((A k) = t)) →
    ((count_eq A (k + 1) t) = ((count_eq A k t) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (t : Int),
  (∀ k : Int, (((k ≥ 0) ∧ ((A k) ≠ t)) →
    ((count_eq A (k + 1) t) = (count_eq A k t))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough
    (n c t i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count_eq A i t)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : ((i < n) ∧ ((A i) = t)))
    (h_trans_c : c' = (c + 1))
    (h_trans_i : i' = (i + 1)) :
    ((c' = (count_eq A i' t))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  obtain ⟨h_loop, h_branch⟩ := h_guard
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : count_eq A (i + 1) t = count_eq A i t + 1 :=
      user_axiom_1 A t i ⟨h_tau_1, h_branch⟩
    rw [h_trans_c, h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
