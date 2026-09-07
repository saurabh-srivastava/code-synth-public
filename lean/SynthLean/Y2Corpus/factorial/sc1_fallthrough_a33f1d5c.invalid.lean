/-
Companion to `sc1_fallthrough_class_1.failed.lean`.

VERDICT: genuinely INVALID — same root cause as class 0.  The extra
`h_tau_1 : n ≥ 0` doesn't help; the counterexample lives at i = 0
where user_axiom_1's `k ≥ 0` precondition with k = i - 1 = -1 fails.

Counterexample: n = 0, i = 0, result = fact(-1), result' = 0, i' = 1.
First conjunct of the goal (`result' = fact(i' - 1)`) reduces to
`0 = fact(0) = 1` via user_axiom_0; that's the contradiction.  The
second conjunct (`n ≥ 0`) holds trivially.
-/
import SynthLean.Basic
open SynthLean

axiom fact : Int → Int
axiom user_axiom_0 : ((fact 0) = 1)
axiom user_axiom_1 : (∀ k : Int, ((k ≥ 0) → ((fact (k + 1)) = ((k + 1) * (fact k)))))

namespace SynthLean.VerifyTmp

theorem sc1_fallthrough_a33f1d5c_is_invalid :
    ∃ (n result i result' i' : Int),
      (n ≥ 0) ∧
      (result = fact (i - 1)) ∧
      (n ≥ 0) ∧
      (i ≤ n) ∧
      (result' = result * i) ∧
      (i' = i + 1) ∧
      ¬ ((result' = fact (i' - 1)) ∧ (n ≥ 0)) := by
  refine ⟨0, fact (-1), 0, 0, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl _              -- 0 ≥ 0
  · norm_num                     -- fact(-1) = fact(0 - 1)
  · exact le_refl _              -- 0 ≥ 0 (h_tau_1)
  · exact le_refl _              -- 0 ≤ 0
  · ring                         -- 0 = fact(-1) * 0
  · rfl                          -- 1 = 0 + 1
  · intro ⟨h, _⟩
    rw [show ((1 : Int) - 1) = 0 from by ring] at h
    rw [user_axiom_0] at h
    exact absurd h (by decide)

end SynthLean.VerifyTmp
