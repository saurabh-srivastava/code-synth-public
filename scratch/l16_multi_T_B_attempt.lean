/-
T_B two-pointer sc1 helper.  Goal: invariant
  { 0 ≤ left, left + right == n - 1, MI, c == 2*left }
preserved by `M' = store(store M left right) right left`,
`left' = left + 1`, `right' = right - 1`, `c' = c + 2`.

For MI preservation, case-split on k = right, k = left, else.
left ≠ right by h_guard.
-/
import SynthLean.Basic
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc1_fallthrough
    (n c left right : Int)
    (M : Int → Int)
    (G : Int → Int → Int)
    (c' left' right' : Int)
    (M' : Int → Int)
    (h_pre : ((n ≥ 0) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < n)) → ((M k) = (-1)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n)) → (((G p) q) = ((G q) p)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n) ∧ (p ≠ q)) → (((G p) q) ≥ 1)))))
    (h_tau_0 : (0 ≤ left))
    (h_tau_1 : ((left + right) = (n - 1)))
    (h_tau_2 : (∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M k) ≠ (-1))) → ((0 ≤ (M k)) ∧ ((M k) < n) ∧ (((G k) (M k)) ≥ 1)))))
    (h_tau_3 : (c = (2 * left)))
    (h_guard : (left < right))
    (h_trans_M : M' = (store (store M left right) right left))
    (h_trans_left : left' = (left + 1))
    (h_trans_right : right' = (right - 1))
    (h_trans_c : c' = (c + 2)) :
    ((0 ≤ left')) ∧ (((left' + right') = (n - 1))) ∧ ((∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n) ∧ (((G k) (M' k)) ≥ 1))))) ∧ ((c' = (2 * left'))) := by
  obtain ⟨h_pre_n, h_pre_init, h_pre_sym, h_pre_clique⟩ := h_pre
  subst h_trans_M
  subst h_trans_left
  subst h_trans_right
  subst h_trans_c
  refine ⟨by omega, by omega, ?_, by omega⟩
  intro k hk
  obtain ⟨hk0, hkn, hkneq⟩ := hk
  -- Bounds we'll need: 0 ≤ right < n, left < n.
  have h_right_lt : right < n := by omega
  have h_right_ge : 0 ≤ right := by omega
  have h_left_lt : left < n := by omega
  have h_left_ne_right : left ≠ right := by omega
  by_cases hk_right : k = right
  · -- k = right: M'[right] = left.
    have hval : store (store M left right) right left k = left := by
      simp [store, hk_right]
    rw [hval] at hkneq ⊢
    refine ⟨h_tau_0, h_left_lt, ?_⟩
    -- G[right][left] = G[left][right] (sym) and G[left][right] ≥ 1 (clique).
    have hsym : G right left = G left right :=
      h_pre_sym right left ⟨h_right_ge, h_right_lt, h_tau_0, h_left_lt⟩
    have hedge : G left right ≥ 1 :=
      h_pre_clique left right
        ⟨h_tau_0, h_left_lt, h_right_ge, h_right_lt, h_left_ne_right⟩
    rw [hk_right, hsym]; exact hedge
  · by_cases hk_left : k = left
    · -- k = left: M'[left] = right.
      have hval : store (store M left right) right left k = right := by
        simp [store, hk_left, h_left_ne_right]
      rw [hval] at hkneq ⊢
      refine ⟨h_right_ge, h_right_lt, ?_⟩
      have hedge : G left right ≥ 1 :=
        h_pre_clique left right
          ⟨h_tau_0, h_left_lt, h_right_ge, h_right_lt, h_left_ne_right⟩
      rw [hk_left]; exact hedge
    · -- k ≠ left, k ≠ right: M'[k] = M[k].
      have hval : store (store M left right) right left k = M k := by
        simp [store, hk_left, hk_right]
      rw [hval] at hkneq ⊢
      exact h_tau_2 k ⟨hk0, hkn, hkneq⟩
end SynthLean.VerifyTmp
