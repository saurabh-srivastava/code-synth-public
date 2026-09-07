/-
gcd's loop-inductive, BRANCH 1 (a < b).  Transition: b := b - a.

Argument: by symmetry (user_axiom_0), gcd_uf(a, b) = gcd_uf(b, a).
Then apply user_axiom_2 at (b, a) (precondition b > a ∧ a > 0) →
gcd_uf(b, a) = gcd_uf(b - a, a).  Combine with h_tau_2.
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
theorem sc4_fallthrough
    (a0 b0 g a b : Int)
    (b' : Int)
    (h_pre : ((a0 > 0) ∧ (b0 > 0)))
    (h_tau_0 : (a > 0))
    (h_tau_1 : (b > 0))
    (h_tau_2 : ((gcd_uf a b) = (gcd_uf a0 b0)))
    (h_guard : ((a ≠ b) ∧ (a < b)))
    (h_trans_b : b' = (b - a)) :
    ((a > 0)) ∧ ((b' > 0)) ∧ (((gcd_uf a b') = (gcd_uf a0 b0))) := by
  obtain ⟨h_neq, h_lt⟩ := h_guard
  refine ⟨h_tau_0, ?_, ?_⟩
  · -- b' = b - a > 0 from b > a
    rw [h_trans_b]; omega
  · -- gcd_uf(a, b - a) = gcd_uf(a0, b0)
    -- Symmetry first: gcd_uf(a, b) = gcd_uf(b, a).
    have h_sym_ab : gcd_uf a b = gcd_uf b a :=
      user_axiom_0 a b ⟨h_tau_0, h_tau_1⟩
    -- Subtraction: gcd_uf(b, a) = gcd_uf(b - a, a).
    have h_rec : gcd_uf b a = gcd_uf (b - a) a :=
      user_axiom_2 b a ⟨h_lt, h_tau_0⟩
    -- Symmetry back: gcd_uf(b - a, a) = gcd_uf(a, b - a).
    have h_b_minus_a_pos : (b - a) > 0 := by omega
    have h_sym_back : gcd_uf (b - a) a = gcd_uf a (b - a) :=
      user_axiom_0 (b - a) a ⟨h_b_minus_a_pos, h_tau_0⟩
    rw [h_trans_b, ← h_sym_back, ← h_rec, ← h_sym_ab, h_tau_2]

end SynthLean.VerifyTmp
