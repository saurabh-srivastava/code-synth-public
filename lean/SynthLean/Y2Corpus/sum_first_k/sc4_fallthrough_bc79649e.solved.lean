/-
sum_first_k's chain-bundle (post) obligation.
From h_tau_2 (i' ≤ k) ∧ h_not_g (¬(i' < k)) ∧ h_tau_1 (0 ≤ i'):
i' = k.  Substitute into h_tau_0: s' = sum(A, k).
-/
import SynthLean.Core
open SynthLean

axiom sum : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((sum A 0) = 0)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ j : Int,
    ((j ≥ 0) → ((sum A (j + 1)) = ((sum A j) + (A j)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n k s i : Int)
    (A : Int → Int)
    (s' i' : Int)
    (h_pre : ((0 ≤ k) ∧ (k ≤ n)))
    (h_tau_0 : (s' = (sum A i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ k))
    (h_not_g : ¬ ((i' < k))) :
    (s' = (sum A k)) := by
  have h_i : i' = k := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
