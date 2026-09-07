/-
array_product's chain-bundle (post) obligation for chosen τ =
{p = prod(A, i), 0 ≤ i, i ≤ n}.

Argument: from h_tau_2 (i' ≤ n) ∧ h_not_g (¬(i' < n)) ∧ h_tau_1
(0 ≤ i'): i' = n.  Substitute into h_tau_0: p' = prod(A, n).
-/
import SynthLean.Core
open SynthLean

axiom prod : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((prod A 0) = 1)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ k : Int,
    ((k ≥ 0) → ((prod A (k + 1)) = ((prod A k) * (A k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n p i : Int)
    (A : Int → Int)
    (p' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (p' = (prod A i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    (p' = (prod A n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
