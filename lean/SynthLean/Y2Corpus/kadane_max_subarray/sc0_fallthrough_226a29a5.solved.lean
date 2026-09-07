/-
kadane_max_subarray entry-bundle for τ subset C4, C6.
Goal conjuncts after init (best'=A[0], cur'=A[0], i'=1):
  C4, C6

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
    ((∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i' - 1)) ∧ ((sum_range A p i') = cur')))) ∧ ((best' ≥ cur')) := by
  subst_eqs
  refine ⟨?_, ?_⟩
  · refine ⟨0, ?_, ?_, ?_⟩
    · omega
    · omega
    · have h1 := user_axiom_1 A 0 0 (le_refl 0)
      have h0 := user_axiom_0 A 0
      simp [h0] at h1
      exact h1
  · rfl

end SynthLean.VerifyTmp
