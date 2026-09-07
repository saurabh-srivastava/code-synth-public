/-
sc2 (branch 0: edge exists, pair (i, i+1)) for τ =
{0 ≤ i, i ≤ n, matching-invariant}.  Case-split on
k = i, k = i+1, otherwise.  No UT needed since UT isn't in
this subset.
-/
import SynthLean.Core
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc2_fallthrough
    (n i : Int)
    (M : Int → Int)
    (G : Int → Int → Int)
    (i' : Int)
    (M' : Int → Int)
    (h_pre : ((n ≥ 0) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < n)) → ((M k) = (-1)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n)) → (((G p) q) = ((G q) p))))))
    (h_tau_0 : (0 ≤ i))
    (h_tau_1 : (i ≤ n))
    (h_tau_2 : (∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M k) ≠ (-1))) → ((0 ≤ (M k)) ∧ ((M k) < n) ∧ (((G k) (M k)) ≥ 1)))))
    (h_guard : ((i < (n - 1)) ∧ (((G i) (i + 1)) ≥ 1)))
    (h_trans_M : M' = (store (store M i (i + 1)) (i + 1) i))
    (h_trans_i : i' = (i + 2)) :
    ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n) ∧ (((G k) (M' k)) ≥ 1))))) := by
  obtain ⟨h_pre_n, h_pre_init, h_pre_sym⟩ := h_pre
  obtain ⟨h_g_lt, h_g_edge⟩ := h_guard
  subst h_trans_M
  subst h_trans_i
  refine ⟨by omega, by omega, ?_⟩
  intro k hk
  obtain ⟨hk0, hkn, hkneq⟩ := hk
  by_cases hk1 : k = i + 1
  · have hval : store (store M i (i + 1)) (i + 1) i k = i := by
      simp [store, hk1]
    rw [hval] at hkneq ⊢
    refine ⟨h_tau_0, by omega, ?_⟩
    have hsym : G (i + 1) i = G i (i + 1) :=
      h_pre_sym (i + 1) i ⟨by omega, by omega, h_tau_0, by omega⟩
    rw [hk1, hsym]; exact h_g_edge
  · by_cases hki : k = i
    · have hval : store (store M i (i + 1)) (i + 1) i k = i + 1 := by
        simp [store, hki, hk1]
      rw [hval] at hkneq ⊢
      refine ⟨by omega, by omega, ?_⟩
      rw [hki]; exact h_g_edge
    · have hval : store (store M i (i + 1)) (i + 1) i k = M k := by
        simp [store, hki, hk1]
      rw [hval] at hkneq ⊢
      exact h_tau_2 k ⟨hk0, hkn, hkneq⟩
end SynthLean.VerifyTmp
