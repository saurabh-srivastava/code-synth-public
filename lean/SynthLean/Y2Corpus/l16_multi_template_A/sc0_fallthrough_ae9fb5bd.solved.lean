/-
T_A sc0 (loop-entry bundle) for full τ.  At entry, M is the pre's
all-(-1) array, so the MI conjunct is vacuous (no k satisfies the
antecedent M[k] ≠ -1).  Other conjuncts close by omega from the
init transitions i' = 0, c' = 0.
-/
import SynthLean.Core
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc0_fallthrough
    (n c i : Int)
    (M : Int → Int)
    (G : Int → Int → Int)
    (c' i' : Int)
    (h_pre : ((n ≥ 0) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < n)) → ((M k) = (-1)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n)) → (((G p) q) = ((G q) p)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n) ∧ (p ≠ q)) → (((G p) q) ≥ 1)))))
    (h_init_i : i' = 0)
    (h_init_c : c' = 0) :
    ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M k) ≠ (-1))) → ((0 ≤ (M k)) ∧ ((M k) < n) ∧ (((G k) (M k)) ≥ 1))))) ∧ ((c' ≥ i')) := by
  obtain ⟨h_pre_n, h_pre_init, _, _⟩ := h_pre
  refine ⟨by omega, by omega, ?_, by omega⟩
  intro k hk
  obtain ⟨hk0, hkn, hkneq⟩ := hk
  exact absurd (h_pre_init k ⟨hk0, hkn⟩) hkneq
end SynthLean.VerifyTmp
