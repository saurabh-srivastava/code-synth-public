/-
verina_basic_80 (only_once) — loop-inductive, BRANCH 1
(A[i] != key).  Transition: i := i+1 (c unchanged).
Argument: user_axiom_2 at k = i with (i ≥ 0 ∧ A i ≠ key) →
count_occ(A,key,i+1) = count_occ(A,key,i).
-/
import SynthLean.Core
open SynthLean

axiom count_occ : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (key : Int), ((count_occ A key 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) = key)) → ((count_occ A key (k + 1)) = ((count_occ A key k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) ≠ key)) → ((count_occ A key (k + 1)) = (count_occ A key k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc4_fallthrough
    (n key result c i : Int)
    (A : Int → Int)
    (i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count_occ A key i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_tau_3 : (n ≥ 0))
    (h_guard : ((i < n) ∧ ((A i) ≠ key)))
    (h_trans_i : i' = (i + 1)) :
    ((c = (count_occ A key i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((n ≥ 0)) := by
  obtain ⟨h_loop, h_branch⟩ := h_guard
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_rec : count_occ A key (i + 1) = count_occ A key i :=
      user_axiom_2 A key i ⟨h_tau_1, h_branch⟩
    rw [h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega
  · omega

end SynthLean.VerifyTmp
