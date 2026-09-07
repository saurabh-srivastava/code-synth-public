/-
sum_array's loop-inductive obligation for chosen τ =
{0≤i, i≤n, s = sum(A, i)}.

After substituting transitions (s' = s + A[i], i' = i + 1), the
three conjuncts reduce to:
  1. 0 ≤ i + 1            — omega.
  2. i + 1 ≤ n             — omega from h_guard (i < n).
  3. s + A[i] = sum(A, i+1) — apply user_axiom_1 at k = i
     (precondition i ≥ 0 from h_tau_0), giving
     sum(A, i+1) = sum(A, i) + A[i].  Rewrite h_tau_2 and ring.
-/
import SynthLean.Core
open SynthLean

axiom sum : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((sum A 0) = 0)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ k : Int,
    ((k ≥ 0) → ((sum A (k + 1)) = ((sum A k) + (A k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n s i : Int)
    (A : Int → Int)
    (s' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (0 ≤ i))
    (h_tau_1 : (i ≤ n))
    (h_tau_2 : (s = (sum A i)))
    (h_guard : (i < n))
    (h_trans_s : s' = (s + (A i)))
    (h_trans_i : i' = (i + 1)) :
    ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((s' = (sum A i'))) := by
  subst h_trans_s h_trans_i
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · have h_rec : sum A (i + 1) = sum A i + A i :=
      user_axiom_1 A i h_tau_0
    rw [h_rec, h_tau_2]

end SynthLean.VerifyTmp
