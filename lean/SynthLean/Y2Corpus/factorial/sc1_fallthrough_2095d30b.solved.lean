/-
Companion to `sc1_fallthrough_2095d30b.failed.lean`.

VERDICT: VALID.  This τ subset {result=fact(i-1), i≥1, i≤n+1} is
inductive over the loop body.  Lean's generic tactic chain can't
close it because the recurrence axiom `user_axiom_1` needs to be
instantiated at `k = i - 1` and rewritten directionally — which
generic search doesn't discover.

The proof:
  - Substitute the transitions to get result' = result*i and i' = i+1.
  - Conjunct 1: result*i = fact((i+1)-1) = fact i.  Apply
    user_axiom_1 at k = i-1 (precondition: i-1 ≥ 0, i.e., i ≥ 1
    from h_tau_1) to get fact i = i * fact(i-1).  Combine with
    h_tau_0 (result = fact(i-1)) and ring.
  - Conjunct 2: i+1 ≥ 1.  Follows from i ≥ 1 (h_tau_1).
  - Conjunct 3: i+1 ≤ n+1.  Follows from h_guard (i ≤ n).
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
    (h_guard : (i ≤ n))
    (h_trans_result : result' = (result * i))
    (h_trans_i : i' = (i + 1)) :
    ((result' = (fact (i' - 1)))) ∧ ((i' ≥ 1)) ∧ ((i' ≤ (n + 1))) := by
  subst h_trans_result h_trans_i
  refine ⟨?_, ?_, ?_⟩
  -- Conjunct 1: result * i = fact ((i + 1) - 1)
  · have h_k_nonneg : (i - 1) ≥ 0 := by omega
    have h_rec : fact ((i - 1) + 1) = ((i - 1) + 1) * fact (i - 1) :=
      user_axiom_1 (i - 1) h_k_nonneg
    have h_k : (i - 1) + 1 = i := by ring
    rw [h_k] at h_rec
    -- h_rec : fact i = i * fact (i - 1)
    have h_goal_idx : (i + 1) - 1 = i := by ring
    rw [h_goal_idx, h_rec, h_tau_0]
    ring
  · omega
  · omega

end SynthLean.VerifyTmp
