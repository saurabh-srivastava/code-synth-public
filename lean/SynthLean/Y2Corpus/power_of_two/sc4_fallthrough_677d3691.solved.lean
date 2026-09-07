/-
power_of_two's chain-bundle (post) obligation.
At exit: r = pow2(i), 0 ≤ i ≤ n, ¬(i < n) ⇒ i = n.
Then r = pow2(n).
-/
import SynthLean.Core
open SynthLean

axiom pow2 : Int → Int
axiom user_axiom_0 : ((pow2 0) = 1)
axiom user_axiom_1 :
  (∀ k : Int, ((k ≥ 0) → ((pow2 (k + 1)) = (2 * (pow2 k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n r i : Int)
    (r' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (r' = (pow2 i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    (r' = (pow2 n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
