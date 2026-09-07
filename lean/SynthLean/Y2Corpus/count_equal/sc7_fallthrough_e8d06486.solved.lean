/-
count_equal's chain-bundle (post) obligation for chosen τ =
{c = count_eq(A, i, t), 0 ≤ i, i ≤ n}.

Argument: from h_tau_2 (i' ≤ n) ∧ h_not_g (¬(i' < n)) ∧ h_tau_1
(0 ≤ i'): i' = n.  Substitute into h_tau_0:
  c' = count_eq(A, n, t).
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
theorem sc7_fallthrough
    (n c t i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c' = (count_eq A i' t)))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    (c' = (count_eq A n t)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
