/-
power_of_two's loop-inductive obligation for chosen τ =
{r = pow2(i), 0 ≤ i, i ≤ n}.

Body: r' = 2*r, i' = i+1.  Apply user_axiom_1 at k=i
(precondition i ≥ 0) → pow2(i+1) = 2 * pow2(i).
-/
import SynthLean.Core
open SynthLean

axiom pow2 : Int → Int
axiom user_axiom_0 : ((pow2 0) = 1)
axiom user_axiom_1 :
  (∀ k : Int, ((k ≥ 0) → ((pow2 (k + 1)) = (2 * (pow2 k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n r i : Int)
    (r' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (r = (pow2 i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : (i < n))
    (h_trans_r : r' = (2 * r))
    (h_trans_i : i' = (i + 1)) :
    ((r' = (pow2 i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : pow2 (i + 1) = 2 * pow2 i :=
      user_axiom_1 i h_tau_1
    rw [h_trans_r, h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
