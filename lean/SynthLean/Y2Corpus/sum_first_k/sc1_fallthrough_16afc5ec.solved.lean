/-
sum_first_k's loop-inductive obligation for chosen τ =
{s = sum(A, i), 0 ≤ i, i ≤ k}.

Body: s' = s + A[i], i' = i+1.  Apply user_axiom_1 at j = i
(j ≥ 0 from h_tau_1) → sum(A, i+1) = sum(A, i) + A[i].
-/
import SynthLean.Core
open SynthLean

axiom sum : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((sum A 0) = 0)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ j : Int,
    ((j ≥ 0) → ((sum A (j + 1)) = ((sum A j) + (A j)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n k s i : Int)
    (A : Int → Int)
    (s' i' : Int)
    (h_pre : ((0 ≤ k) ∧ (k ≤ n)))
    (h_tau_0 : (s = (sum A i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ k))
    (h_guard : (i < k))
    (h_trans_s : s' = (s + (A i)))
    (h_trans_i : i' = (i + 1)) :
    ((s' = (sum A i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ k)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : sum A (i + 1) = sum A i + A i :=
      user_axiom_1 A i h_tau_1
    rw [h_trans_s, h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
