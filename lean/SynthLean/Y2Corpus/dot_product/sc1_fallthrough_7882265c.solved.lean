/-
dot_product's loop-inductive obligation for chosen τ =
{s = dot(A, B, i), 0 ≤ i, i ≤ n}.

After substituting transitions (s' = s + A[i]*B[i], i' = i+1):
  1. s + A[i]*B[i] = dot(A, B, i+1) — apply user_axiom_1 at k=i
     (i ≥ 0 from h_tau_1).
  2. 0 ≤ i+1, i+1 ≤ n — omega + h_guard.
-/
import SynthLean.Core
open SynthLean

axiom dot : (Int → Int) → (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (B : Int → Int),
  ((dot A B 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (B : Int → Int),
  (∀ k : Int, ((k ≥ 0) →
    ((dot A B (k + 1)) = ((dot A B k) + ((A k) * (B k))))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n s i : Int)
    (A B : Int → Int)
    (s' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (s = (dot A B i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : (i < n))
    (h_trans_s : s' = (s + ((A i) * (B i))))
    (h_trans_i : i' = (i + 1)) :
    ((s' = (dot A B i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : dot A B (i + 1) = dot A B i + A i * B i :=
      user_axiom_1 A B i h_tau_1
    rw [h_trans_s, h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
