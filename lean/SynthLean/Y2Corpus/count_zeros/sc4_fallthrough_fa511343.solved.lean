/-
count_zeros' loop-inductive obligation, BRANCH 1 (A[i] ≠ 0).
τ = {c = count(A, i), 0 ≤ i, i ≤ n}.  Transition: i := i+1 only;
c stays unchanged at this branch.

Argument:
  - From h_guard: (i < n) ∧ (A i ≠ 0).
  - From user_axiom_2 at k = i (precondition i ≥ 0 ∧ A i ≠ 0):
    count(A, i+1) = count(A, i).
  - h_tau_0 gives c = count(A, i).  After substitution: c = count(A, i+1).
-/
import SynthLean.Core
open SynthLean

axiom count : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((count A 0) = 0)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ k : Int,
    (((k ≥ 0) ∧ ((A k) = 0)) → ((count A (k + 1)) = ((count A k) + 1))))
axiom user_axiom_2 :
  ∀ (A : Int → Int), (∀ k : Int,
    (((k ≥ 0) ∧ ((A k) ≠ 0)) → ((count A (k + 1)) = (count A k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n c i : Int)
    (A : Int → Int)
    (i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count A i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : ((i < n) ∧ ((A i) ≠ 0)))
    (h_trans_i : i' = (i + 1)) :
    ((c = (count A i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  obtain ⟨h_loop, h_branch⟩ := h_guard
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : count A (i + 1) = count A i :=
      user_axiom_2 A i ⟨h_tau_1, h_branch⟩
    rw [h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
