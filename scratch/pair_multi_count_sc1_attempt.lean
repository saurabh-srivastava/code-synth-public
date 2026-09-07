/-
sc1 (Cand 0 full-pair) for τ = {0 ≤ i, i ≤ n, MI, c ≥ i}.
Same case-split as cb44bbf0 for the MI conjunct, plus a 4th
`c' >= i'` conjunct from c+2 >= i+2.
-/
import SynthLean.Basic
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc1_fallthrough
    (n c i : Int)
    (M : Int → Int)
    (G : Int → Int → Int)
    (c' i' : Int)
    (M' : Int → Int)
    (h_pre : ((n ≥ 0) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < n)) → ((M k) = (-1)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n)) → (((G p) q) = ((G q) p)))) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < (n - 1))) → (((G k) (k + 1)) ≥ 1)))))
    (h_tau_0 : (0 ≤ i))
    (h_tau_1 : (i ≤ n))
    (h_tau_2 : (∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M k) ≠ (-1))) → ((0 ≤ (M k)) ∧ ((M k) < n) ∧ (((G k) (M k)) ≥ 1)))))
    (h_tau_3 : (c ≥ i))
    (h_guard : (i < (n - 1)))
    (h_trans_M : M' = (store (store M i (i + 1)) (i + 1) i))
    (h_trans_i : i' = (i + 2))
    (h_trans_c : c' = (c + 2)) :
    ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n) ∧ (((G k) (M' k)) ≥ 1))))) ∧ ((c' ≥ i')) := by
  obtain ⟨h_pre_n, h_pre_init, h_pre_sym, h_pre_chain⟩ := h_pre
  subst h_trans_M
  subst h_trans_i
  subst h_trans_c
  refine ⟨by omega, by omega, ?_, by omega⟩
  -- Matching-invariant preservation: same case-split as cb44bbf0.
  intro k hk
  obtain ⟨hk0, hkn, hkneq⟩ := hk
  by_cases hk1 : k = i + 1
  · have hval : store (store M i (i + 1)) (i + 1) i k = i := by
      simp [store, hk1]
    rw [hval] at hkneq ⊢
    refine ⟨h_tau_0, by omega, ?_⟩
    have hsym : G (i + 1) i = G i (i + 1) :=
      h_pre_sym (i + 1) i ⟨by omega, by omega, h_tau_0, by omega⟩
    have hedge : G i (i + 1) ≥ 1 :=
      h_pre_chain i ⟨h_tau_0, by omega⟩
    rw [hk1, hsym]; exact hedge
  · by_cases hki : k = i
    · have hval : store (store M i (i + 1)) (i + 1) i k = i + 1 := by
        simp [store, hki, hk1]
      rw [hval] at hkneq ⊢
      refine ⟨by omega, by omega, ?_⟩
      have hedge : G i (i + 1) ≥ 1 :=
        h_pre_chain i ⟨h_tau_0, by omega⟩
      rw [hki]; exact hedge
    · have hval : store (store M i (i + 1)) (i + 1) i k = M k := by
        simp [store, hki, hk1]
      rw [hval] at hkneq ⊢
      exact h_tau_2 k ⟨hk0, hkn, hkneq⟩
end SynthLean.VerifyTmp
