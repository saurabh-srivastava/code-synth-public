/-
C1 greedy-match sc7 (post-bundle) for full τ.
At loop exit, ¬g gives i' ≥ m, combined with τ's i' ≤ m
gives i' = m.  Then maximal-up-to-i' coincides with the
maximal post (j < m).
-/
import SynthLean.Core
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc7_fallthrough
    (m n i : Int)
    (edges M : Int → Int)
    (i' : Int)
    (M' : Int → Int)
    (h_pre : ((n ≥ 0) ∧ (m ≥ 0) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < n)) → ((M k) = (-1)))) ∧ (∀ j : Int, (((0 ≤ j) ∧ (j < m)) → ((0 ≤ (edges (2 * j))) ∧ ((edges (2 * j)) < n) ∧ (0 ≤ (edges ((2 * j) + 1))) ∧ ((edges ((2 * j) + 1)) < n) ∧ ((edges (2 * j)) ≠ (edges ((2 * j) + 1))))))))
    (h_tau_0 : (0 ≤ i'))
    (h_tau_1 : (i' ≤ m))
    (h_tau_2 : (∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n)))))
    (h_tau_3 : (∀ j : Int, (((0 ≤ j) ∧ (j < i')) → (¬ (((M' (edges (2 * j))) = (-1)) ∧ ((M' (edges ((2 * j) + 1))) = (-1)))))))
    (h_not_g : ¬ ((i' < m))) :
    ((∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n)))) ∧ (∀ j : Int, (((0 ≤ j) ∧ (j < m)) → (¬ (((M' (edges (2 * j))) = (-1)) ∧ ((M' (edges ((2 * j) + 1))) = (-1))))))) := by
  refine ⟨h_tau_2, ?_⟩
  intro j ⟨hj0, hjm⟩
  -- From h_tau_1 (i' ≤ m) and h_not_g (i' ≥ m), i' = m.
  -- So j < m = i', and h_tau_3 applies.
  exact h_tau_3 j ⟨hj0, by omega⟩
end SynthLean.VerifyTmp
