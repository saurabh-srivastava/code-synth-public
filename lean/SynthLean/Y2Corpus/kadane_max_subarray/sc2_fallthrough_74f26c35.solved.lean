/-
kadane_max_subarray sc2 (branch 0: cur + A[i] ≥ A[i] — extend run)
inductive for τ subset {cur_ub, witness}.

Transition: cur' = cur + A[i], best' = max(best, cur + A[i]), i' = i + 1.
-/
import SynthLean.Core
open SynthLean

axiom sum_range : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ p : Int, ((sum_range A p p) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ p q : Int, ((p ≤ q) → ((sum_range A p (q + 1)) = ((sum_range A p q) + (A q)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough
    (n best i cur : Int)
    (A : Int → Int)
    (best' i' cur' : Int)
    (h_pre : (n ≥ 1))
    (h_tau_0 : (∀ p : Int, (((0 ≤ p) ∧ (p ≤ (i - 1))) → ((sum_range A p i) ≤ cur))))
    (h_tau_1 : (∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i - 1)) ∧ ((sum_range A p i) = cur))))
    (h_guard : ((i < n) ∧ ((cur + (A i)) ≥ (A i))))
    (h_trans_cur : cur' = (cur + (A i)))
    (h_trans_best : best' = (if (best ≥ (cur + (A i))) then best else (cur + (A i))))
    (h_trans_i : i' = (i + 1)) :
    ((∀ p : Int, (((0 ≤ p) ∧ (p ≤ (i' - 1))) → ((sum_range A p i') ≤ cur')))) ∧ ((∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i' - 1)) ∧ ((sum_range A p i') = cur')))) := by
  subst_eqs
  refine ⟨?_, ?_⟩
  · obtain ⟨h_lt, h_cur_nn_guard⟩ := h_guard
    have h_cur_nn : cur ≥ 0 := by omega
    intro p hp
    obtain ⟨hp0, hp1⟩ := hp
    have h_step : sum_range A p (i + 1) = sum_range A p i + A i := by
      exact user_axiom_1 A p i (by omega)
    by_cases hpi : p = i
    · subst hpi
      rw [h_step]
      have h_self : sum_range A p p = 0 := user_axiom_0 A p
      rw [h_self]
      omega
    · have hp_lt_i : p ≤ i - 1 := by omega
      have h_bound := h_tau_0 p ⟨hp0, hp_lt_i⟩
      rw [h_step]
      omega
  · obtain ⟨p_star, h_p0, h_p1, h_sum⟩ := h_tau_1
    refine ⟨p_star, ?_, ?_, ?_⟩
    · exact h_p0
    · omega
    · have h_step : sum_range A p_star (i + 1) = sum_range A p_star i + A i := by
        exact user_axiom_1 A p_star i (by omega)
      rw [h_step, h_sum]

end SynthLean.VerifyTmp
