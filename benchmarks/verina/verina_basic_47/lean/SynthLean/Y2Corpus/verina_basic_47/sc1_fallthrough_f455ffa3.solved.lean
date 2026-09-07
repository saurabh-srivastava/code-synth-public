/-
verina_basic_47 (arraySum) — loop-inductive obligation for chosen τ =
{0 ≤ i, i ≤ n, result = sum(A, i)}.

After substituting the loop transitions (result' = result + A[i],
i' = i + 1), the three conjuncts reduce to:
  1. 0 ≤ i + 1              — omega (from h_tau_0: 0 ≤ i).
  2. i + 1 ≤ n              — omega (from h_guard: i < n).
  3. result + A[i] = sum(A, i+1) — apply user_axiom_1 at k = i
     (precondition i ≥ 0 from h_tau_0), giving
     sum(A, i+1) = sum(A, i) + A[i]; rewrite h_tau_2 and close.
This mirrors sum_array's sc1 (our `sum` re-axiomatizes VERINA's `sumTo`).
-/
import SynthLean.Core
open SynthLean

axiom sum : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((sum A 0) = 0)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ (k : Int),
    ((k ≥ 0) → ((sum A (k + 1)) = ((sum A k) + (A k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n result i : Int)
    (A : Int → Int)
    (result' i' : Int)
    (h_pre : (n ≥ 1))
    (h_tau_0 : (0 ≤ i))
    (h_tau_1 : (i ≤ n))
    (h_tau_2 : (result = (sum A i)))
    (h_guard : (i < n))
    (h_trans_result : result' = (result + (A i)))
    (h_trans_i : i' = (i + 1)) :
    ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((result' = (sum A i'))) := by
  subst h_trans_result h_trans_i
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · have h_rec : sum A (i + 1) = sum A i + A i :=
      user_axiom_1 A i h_tau_0
    rw [h_rec, h_tau_2]

end SynthLean.VerifyTmp
