/-
verina_basic_20 (uniqueProduct) — ranking lower-bound (sc6).
Chosen τ = {p = uprod(A,i), 0 ≤ i, i ≤ n}.
Auto-authored from the translator's exact obligation signature.
-/
import SynthLean.Core
open SynthLean

axiom uprod : (Int → Int) → Int → Int
axiom seen : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((uprod A 0) = 1)
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ (k : Int), (((k ≥ 0) ∧ ((seen A k) = 0)) → ((uprod A (k + 1)) = ((uprod A k) * (A k)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ (k : Int), (((k ≥ 0) ∧ ((seen A k) ≠ 0)) → ((uprod A (k + 1)) = (uprod A k))))
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc6_fallthrough
    (n p i : Int)
    (A : Int → Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (p = (uprod A i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n)) :
    (n - i) ≥ 0 := by
  -- Ranking lower bound: n-i ≥ 0 from i ≤ n.  Pure arithmetic.
  omega
end SynthLean.VerifyTmp
