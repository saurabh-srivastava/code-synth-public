/-
gcd's chain-bundle (post) obligation.

At loop exit: a' > 0, b' > 0, gcd_uf(a', b') = gcd_uf(a0, b0),
and ¬(a' ≠ b') (i.e., a' = b').  Skip: g' = a'.

By user_axiom_1 (idempotent on equal args): gcd_uf(a', a') = a'.
Hence gcd_uf(a', b') = gcd_uf(a', a') = a' = g'.  So
g' = gcd_uf(a0, b0).
-/
import SynthLean.Basic
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
theorem sc7_fallthrough
    (a0 b0 g a b : Int)
    (g' a' b' : Int)
    (h_pre : ((a0 > 0) ∧ (b0 > 0)))
    (h_tau_0 : (a' > 0))
    (h_tau_1 : (b' > 0))
    (h_tau_2 : ((gcd_uf a' b') = (gcd_uf a0 b0)))
    (h_not_g : ¬ ((a' ≠ b')))
    (h_skip_g : g' = a') :
    (g' = (gcd_uf a0 b0)) := by
  have h_eq : a' = b' := by
    by_contra h
    exact h_not_g h
  -- Substitute a' = b' so gcd_uf(a', b') = gcd_uf(a', a')
  rw [← h_eq] at h_tau_2
  -- user_axiom_1 at a' gives gcd_uf(a', a') = a'
  have h_idem : gcd_uf a' a' = a' := user_axiom_1 a' h_tau_0
  rw [h_idem] at h_tau_2
  -- h_tau_2 : a' = gcd_uf a0 b0; h_skip_g : g' = a'
  rw [h_skip_g, h_tau_2]

end SynthLean.VerifyTmp
