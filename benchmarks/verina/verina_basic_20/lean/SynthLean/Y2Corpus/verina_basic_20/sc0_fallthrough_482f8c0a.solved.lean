/-
verina_basic_20 (uniqueProduct) — entry-bundle obligation (sc0).
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
theorem sc0_fallthrough
    (n p i : Int)
    (A : Int → Int)
    (p' i' : Int)
    (h_pre : (n ≥ 0))
    (h_init_p : p' = 1)
    (h_init_i : i' = 0) :
    ((p' = (uprod A i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  -- Entry: p:=1, i:=0.  p=1=uprod(A,0) via base axiom; bounds arithmetic.
  subst_eqs
  refine ⟨?_, ?_, ?_⟩
  · exact (user_axiom_0 A).symm
  · omega
  · omega
end SynthLean.VerifyTmp
