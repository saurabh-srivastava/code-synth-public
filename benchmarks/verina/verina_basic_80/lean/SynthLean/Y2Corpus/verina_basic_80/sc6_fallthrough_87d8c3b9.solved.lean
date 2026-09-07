/-
verina_basic_80 (only_once) — ranking lower-bound (sc6).
φ = n - i ≥ 0 from i ≤ n.  Pure arithmetic.
-/
import SynthLean.Core
open SynthLean

axiom count_occ : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (key : Int), ((count_occ A key 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) = key)) → ((count_occ A key (k + 1)) = ((count_occ A key k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) ≠ key)) → ((count_occ A key (k + 1)) = (count_occ A key k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc6_fallthrough
    (n key result c i : Int)
    (A : Int → Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c = (count_occ A key i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_tau_3 : (n ≥ 0)) :
    (n - i) ≥ 0 := by
  omega

end SynthLean.VerifyTmp
