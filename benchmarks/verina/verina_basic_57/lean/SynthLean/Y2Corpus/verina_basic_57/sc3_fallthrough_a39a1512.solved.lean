/-
verina_basic_57 (CountLessThan) — ranking-decrease, BRANCH 0.
φ = n - i decreases when i := i+1.  Pure arithmetic.
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
theorem sc3_fallthrough
    (n threshold c i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count_less A threshold i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : ((i < n) ∧ ((A i) < threshold)))
    (h_trans_c : c' = (c + 1))
    (h_trans_i : i' = (i + 1)) :
    (n - i) > (n - i') := by
  omega

end SynthLean.VerifyTmp
