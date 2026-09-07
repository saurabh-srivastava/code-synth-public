/-
dot_product's chain-bundle (post) obligation.
From h_tau_2 (i' ≤ n) ∧ h_not_g (¬(i' < n)) ∧ h_tau_1 (0 ≤ i'):
i' = n.  Substitute into h_tau_0: s' = dot(A, B, n).
-/
import SynthLean.Core
open SynthLean

axiom dot : (Int → Int) → (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (B : Int → Int),
  ((dot A B 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (B : Int → Int),
  (∀ k : Int, ((k ≥ 0) →
    ((dot A B (k + 1)) = ((dot A B k) + ((A k) * (B k))))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n s i : Int)
    (A B : Int → Int)
    (s' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (s' = (dot A B i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    (s' = (dot A B n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
