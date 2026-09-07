/-
T_A linear-sweep sc4 (post-bundle) for full τ = {0 ≤ i, i ≤ n,
MI, c >= i}.  Goal splits to MI(M') (h_tau_2) and c' >= n - 1
(from c' >= i' >= n - 1 via h_tau_3 and h_not_g).
-/
import SynthLean.Core
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc4_fallthrough
    (n c i : Int)
    (M : Int → Int)
    (G : Int → Int → Int)
    (c' i' : Int)
    (M' : Int → Int)
    (h_pre : ((n ≥ 0) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < n)) → ((M k) = (-1)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n)) → (((G p) q) = ((G q) p)))) ∧ (∀ p q : Int, (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n) ∧ (p ≠ q)) → (((G p) q) ≥ 1)))))
    (h_tau_0 : (0 ≤ i'))
    (h_tau_1 : (i' ≤ n))
    (h_tau_2 : (∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n) ∧ (((G k) (M' k)) ≥ 1)))))
    (h_tau_3 : (c' ≥ i'))
    (h_not_g : ¬ ((i' < (n - 1)))) :
    ((∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n) ∧ (((G k) (M' k)) ≥ 1)))) ∧ (c' ≥ (n - 1))) :=
  ⟨h_tau_2, by omega⟩
end SynthLean.VerifyTmp
