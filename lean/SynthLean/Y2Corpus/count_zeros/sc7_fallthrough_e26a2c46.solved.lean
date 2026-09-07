/-
count_zeros' chain-bundle (post) obligation for chosen τ =
{c = count(A, i), 0 ≤ i, i ≤ n}.

Argument: from h_tau_2 (i' ≤ n) ∧ h_not_g (¬(i' < n)) ∧ h_tau_1
(0 ≤ i'): i' = n.  Substitute into h_tau_0: c' = count(A, n).
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
theorem sc7_fallthrough
    (n c i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c' = (count A i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    (c' = (count A n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
