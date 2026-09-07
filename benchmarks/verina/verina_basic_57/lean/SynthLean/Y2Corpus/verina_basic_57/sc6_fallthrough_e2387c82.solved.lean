/-
verina_basic_57 (CountLessThan) — ranking lower-bound (sc6).
φ = n - i ≥ 0 from i ≤ n.  Pure arithmetic.
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
theorem sc6_fallthrough
    (n threshold c i : Int)
    (A : Int → Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count_less A threshold i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n)) :
    (n - i) ≥ 0 := by
  omega

end SynthLean.VerifyTmp
