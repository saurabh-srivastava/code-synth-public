/-
Companion to `sc4_fallthrough_08dbe8b7.failed.lean`.

VERDICT: VALID.  This is factorial's chain-bundle (post-bundle)
obligation for the chosen τ = {result=fact(i-1), i≥1, i≤n+1}.

Argument: from h_not_g (¬(i' ≤ n)) and h_tau_2 (i' ≤ n+1) and
h_tau_1 (i' ≥ 1), derive i' = n+1.  Substitute into h_tau_0
(result' = fact(i' - 1) = fact(n+1-1) = fact n).  Conclude.

Lean's generic chain doesn't close this because the `fact n` in
the goal isn't connected to `fact (i' - 1)` in h_tau_0 without
the omega-derived i' = n+1.  Explicit rewrite is needed.
-/
import SynthLean.Basic
open SynthLean

axiom fact : Int → Int
axiom user_axiom_0 : ((fact 0) = 1)
axiom user_axiom_1 : (∀ k : Int, ((k ≥ 0) → ((fact (k + 1)) = ((k + 1) * (fact k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n result i : Int)
    (result' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (result' = (fact (i' - 1))))
    (h_tau_1 : (i' ≥ 1))
    (h_tau_2 : (i' ≤ (n + 1)))
    (h_not_g : ¬ ((i' ≤ n))) :
    (result' = (fact n)) := by
  have h_i : i' = n + 1 := by omega
  rw [h_i] at h_tau_0
  have h_idx : (n + 1) - 1 = n := by ring
  rw [h_idx] at h_tau_0
  exact h_tau_0

end SynthLean.VerifyTmp
