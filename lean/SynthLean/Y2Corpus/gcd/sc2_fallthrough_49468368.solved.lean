/-
gcd's loop-inductive, BRANCH 0 (a > b).  Transition: a := a - b.

Argument: apply user_axiom_2 at (a, b) (precondition a > b ∧
b > 0) → gcd_uf(a, b) = gcd_uf(a - b, b).  Combine with h_tau_2
to get gcd_uf(a - b, b) = gcd_uf(a0, b0).
-/
import SynthLean.Core
open SynthLean

axiom gcd_uf : Int → Int → Int
axiom user_axiom_0 :
  (∀ x : Int, (∀ y : Int, (((x > 0) ∧ (y > 0)) →
    ((gcd_uf x y) = (gcd_uf y x)))))
axiom user_axiom_1 :
  (∀ x : Int, ((x > 0) → ((gcd_uf x x) = x)))
axiom user_axiom_2 :
  (∀ x : Int, (∀ y : Int, (((x > y) ∧ (y > 0)) →
    ((gcd_uf x y) = (gcd_uf (x - y) y)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough
    (a0 b0 g a b : Int)
    (a' : Int)
    (h_pre : ((a0 > 0) ∧ (b0 > 0)))
    (h_tau_0 : (a > 0))
    (h_tau_1 : (b > 0))
    (h_tau_2 : ((gcd_uf a b) = (gcd_uf a0 b0)))
    (h_guard : ((a ≠ b) ∧ (a > b)))
    (h_trans_a : a' = (a - b)) :
    ((a' > 0)) ∧ ((b > 0)) ∧ (((gcd_uf a' b) = (gcd_uf a0 b0))) := by
  obtain ⟨h_neq, h_gt⟩ := h_guard
  refine ⟨?_, h_tau_1, ?_⟩
  · -- a' = a - b > 0 from a > b
    rw [h_trans_a]; omega
  · -- gcd_uf(a - b, b) = gcd_uf(a0, b0)
    have h_rec : gcd_uf a b = gcd_uf (a - b) b :=
      user_axiom_2 a b ⟨h_gt, h_tau_1⟩
    rw [h_trans_a, ← h_rec, h_tau_2]

end SynthLean.VerifyTmp
