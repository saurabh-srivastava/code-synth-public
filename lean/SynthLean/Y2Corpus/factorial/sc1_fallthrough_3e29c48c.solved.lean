/-
Companion to `sc1_fallthrough_3e29c48c.failed.lean`.

VERDICT: VALID.  τ = {result=fact(i-1), i≥1, i≤n+1, n≥0} —
the full 4-atom τ.  Goal conjoins all four post-state atoms.
-/
import SynthLean.Basic
open SynthLean

axiom fact : Int → Int
axiom user_axiom_0 : ((fact 0) = 1)
axiom user_axiom_1 : (∀ k : Int, ((k ≥ 0) → ((fact (k + 1)) = ((k + 1) * (fact k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n result i : Int)
    (result' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (result = (fact (i - 1))))
    (h_tau_1 : (i ≥ 1))
    (h_tau_2 : (i ≤ (n + 1)))
    (h_tau_3 : (n ≥ 0))
    (h_guard : (i ≤ n))
    (h_trans_result : result' = (result * i))
    (h_trans_i : i' = (i + 1)) :
    ((result' = (fact (i' - 1)))) ∧ ((i' ≥ 1)) ∧ ((i' ≤ (n + 1))) ∧ ((n ≥ 0)) := by
  subst h_trans_result h_trans_i
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_k_nonneg : (i - 1) ≥ 0 := by omega
    have h_rec : fact ((i - 1) + 1) = ((i - 1) + 1) * fact (i - 1) :=
      user_axiom_1 (i - 1) h_k_nonneg
    have h_k : (i - 1) + 1 = i := by ring
    rw [h_k] at h_rec
    have h_goal_idx : (i + 1) - 1 = i := by ring
    rw [h_goal_idx, h_rec, h_tau_0]
    ring
  · omega
  · omega
  · exact h_tau_3

end SynthLean.VerifyTmp
