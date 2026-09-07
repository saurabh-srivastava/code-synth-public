/-
kadane_max_subarray entry-bundle for τ subset C2, C3, C5.
Goal conjuncts after init (best'=A[0], cur'=A[0], i'=1):
  C2, C3, C5

All conjuncts trivially provable from h_pre (n ≥ 1) and user
axioms 0 (sum_range A p p = 0) and 1 (recurrence) at the
single (p, q) values forced by the i'=1 constraint.
-/
import SynthLean.Basic
open SynthLean

axiom sum_range : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ p : Int, ((sum_range A p p) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ p q : Int, ((p ≤ q) → ((sum_range A p (q + 1)) = ((sum_range A p q) + (A q)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc0_fallthrough
    (n best i cur : Int)
    (A : Int → Int)
    (best' i' cur' : Int)
    (h_pre : (n ≥ 1))
    (h_init_best : best' = (A 0))
    (h_init_cur : cur' = (A 0))
    (h_init_i : i' = 1) :
    ((i' ≤ n)) ∧ ((∀ p : Int, (((0 ≤ p) ∧ (p ≤ (i' - 1))) → ((sum_range A p i') ≤ cur')))) ∧ ((∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i')) → ((sum_range A p (q + 1)) ≤ best')))) := by
  subst_eqs
  refine ⟨?_, ?_, ?_⟩
  · omega
  · intro p hp
    obtain ⟨hp0, hp1⟩ := hp
    have h_p_eq : p = 0 := by omega
    subst h_p_eq
    have h_sr : sum_range A 0 1 = A 0 := by
      have h1 := user_axiom_1 A 0 0 (le_refl 0)
      have h0 := user_axiom_0 A 0
      simp [h0] at h1
      exact h1
    rw [h_sr]
  · intro p q hpq
    obtain ⟨hp0, hpq', hq⟩ := hpq
    have h_q_eq : q = 0 := by omega
    have h_p_eq : p = 0 := by omega
    subst h_q_eq
    subst h_p_eq
    show sum_range A 0 1 ≤ A 0
    have h_sr : sum_range A 0 1 = A 0 := by
      have h1 := user_axiom_1 A 0 0 (le_refl 0)
      have h0 := user_axiom_0 A 0
      simp [h0] at h1
      exact h1
    rw [h_sr]

end SynthLean.VerifyTmp
