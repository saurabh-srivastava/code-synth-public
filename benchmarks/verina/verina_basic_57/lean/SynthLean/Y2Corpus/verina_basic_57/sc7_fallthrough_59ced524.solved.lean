/-
verina_basic_57 (CountLessThan) — chain-bundle post (sc7).
From i' ≤ n ∧ ¬(i' < n): i' = n.  Then c' = count_less(A,
threshold,n) via h_tau_0.  Bridges loop exit to the postcondition
c == count_less(A, threshold, n).
-/
import SynthLean.Core
open SynthLean

axiom count_less : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (threshold : Int), ((count_less A threshold 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (threshold : Int),
  (∀ (k : Int), (((k ≥ 0) ∧ ((A k) < threshold)) →
    ((count_less A threshold (k + 1)) = ((count_less A threshold k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (threshold : Int),
  (∀ (k : Int), (((k ≥ 0) ∧ ((A k) ≥ threshold)) →
    ((count_less A threshold (k + 1)) = (count_less A threshold k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc7_fallthrough
    (n threshold c i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c' = (count_less A threshold i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    (c' = (count_less A threshold n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_0

end SynthLean.VerifyTmp
