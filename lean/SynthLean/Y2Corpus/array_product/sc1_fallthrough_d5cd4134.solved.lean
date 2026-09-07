/-
array_product's loop-inductive obligation for chosen τ =
{p = prod(A, i), 0 ≤ i, i ≤ n}.

After substituting transitions (p' = p * A[i], i' = i + 1):
  1. p * A[i] = prod(A, i + 1) — apply user_axiom_1 at k = i
     (precondition i ≥ 0 from h_tau_1).
  2. 0 ≤ i + 1 — omega.
  3. i + 1 ≤ n — omega from h_guard (i < n).
-/
import SynthLean.Core
open SynthLean

axiom prod : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((prod A 0) = 1)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ k : Int,
    ((k ≥ 0) → ((prod A (k + 1)) = ((prod A k) * (A k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n p i : Int)
    (A : Int → Int)
    (p' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (p = (prod A i)))
    (h_tau_1 : (0 ≤ i))
    (h_tau_2 : (i ≤ n))
    (h_guard : (i < n))
    (h_trans_p : p' = (p * (A i)))
    (h_trans_i : i' = (i + 1)) :
    ((p' = (prod A i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_rec : prod A (i + 1) = prod A i * A i :=
      user_axiom_1 A i h_tau_1
    rw [h_trans_p, h_trans_i, h_rec, h_tau_0]
  · rw [h_trans_i]; omega
  · rw [h_trans_i]; omega

end SynthLean.VerifyTmp
