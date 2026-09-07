/-
array_neg_count's chain-bundle (post).
From h_tau_2 (i' ≤ n) ∧ h_not_g (¬(i' < n)) ∧ h_tau_1 (0 ≤ i'):
i' = n.  Then c' = count_neg(A, n) via h_tau_0.
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
theorem sc7_fallthrough
    (n c i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c' = (count_neg A i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    (c' = (count_neg A n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
