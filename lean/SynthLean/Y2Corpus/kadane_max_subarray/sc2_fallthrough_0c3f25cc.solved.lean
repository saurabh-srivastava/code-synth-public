/-
kadane_max_subarray sc2 (branch 0: cur + A[i] ≥ A[i] — extend run)
inductive for τ subset {cur_ub, best_ub, best_ge}.

Transition: cur' = cur + A[i], best' = max(best, cur + A[i]), i' = i + 1.
-/
import SynthLean.Basic
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
    (h_tau_1 : (∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i)) → ((sum_range A p (q + 1)) ≤ best))))
    (h_tau_2 : (best ≥ cur))
    (h_guard : ((i < n) ∧ ((cur + (A i)) ≥ (A i))))
    (h_trans_cur : cur' = (cur + (A i)))
    (h_trans_best : best' = (if (best ≥ (cur + (A i))) then best else (cur + (A i))))
    (h_trans_i : i' = (i + 1)) :
    ((∀ p : Int, (((0 ≤ p) ∧ (p ≤ (i' - 1))) → ((sum_range A p i') ≤ cur')))) ∧ ((∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i')) → ((sum_range A p (q + 1)) ≤ best')))) ∧ ((best' ≥ cur')) := by
  subst_eqs
  refine ⟨?_, ?_, ?_⟩
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
  · obtain ⟨h_lt, h_cur_nn_guard⟩ := h_guard
    have h_cur_nn : cur ≥ 0 := by omega
    intro p q hpq
    obtain ⟨hp0, hpq', hq⟩ := hpq
    by_cases hq_eq : q = i
    · subst hq_eq
      -- Need sum_range A p (q+1) ≤ max(best, cur + A i).
      have h_step : sum_range A p (q + 1) = sum_range A p q + A q := by
        exact user_axiom_1 A p q (by omega)
      by_cases hp_eq : p = q
      · subst hp_eq
        rw [h_step]
        have h_self : sum_range A p p = 0 := user_axiom_0 A p
        rw [h_self]
        split_ifs <;> omega
      · have hp_lt_q : p ≤ q - 1 := by omega
        have h_bound := h_tau_0 p ⟨hp0, hp_lt_q⟩
        rw [h_step]
        split_ifs <;> omega
    · have hq_lt_i : q < i := by omega
      have h_bound := h_tau_1 p q ⟨hp0, hpq', hq_lt_i⟩
      split_ifs <;> omega
  · show (if best ≥ cur + A i then best else cur + A i) ≥ cur + A i
    split_ifs <;> omega

end SynthLean.VerifyTmp
