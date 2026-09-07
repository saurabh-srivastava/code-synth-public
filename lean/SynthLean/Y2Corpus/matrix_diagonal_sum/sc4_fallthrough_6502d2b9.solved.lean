/-
matrix_diagonal_sum's chain-bundle (post) obligation for chosen
τ = {0 ≤ i', i' ≤ n, result' = diag_sum(A, n, i')}.

Argument: from h_tau_0 (0 ≤ i'), h_tau_1 (i' ≤ n), and h_not_g
(¬ (i' < n)), we get i' = n by omega.  Substitute into h_tau_2:
result' = diag_sum(A, n, i') = diag_sum(A, n, n).
-/
import SynthLean.Core
open SynthLean

axiom diag_sum : (Int → Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int → Int) (n : Int),
  ((diag_sum A n 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int → Int) (n : Int),
  (∀ (k : Int), ((k ≥ 0) →
    ((diag_sum A n (k + 1)) = ((diag_sum A n k) + ((A k) k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n result i : Int)
    (A : Int → Int → Int)
    (result' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (0 ≤ i'))
    (h_tau_1 : (i' ≤ n))
    (h_tau_2 : (result' = (diag_sum A n i')))
    (h_not_g : ¬ ((i' < n))) :
    (result' = (diag_sum A n n)) := by
  have h_i : i' = n := by omega
  rw [h_i] at h_tau_2; exact h_tau_2

end SynthLean.VerifyTmp
