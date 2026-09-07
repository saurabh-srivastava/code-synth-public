/-
Companion to `sc1_fallthrough_class_2.failed.lean`.

VERDICT: genuinely INVALID — same root cause as class 0.  Adding
`h_tau_1 : i ≤ n + 1` constrains i from above but doesn't help at
the lower-bound counterexample i = 0.

Counterexample: n = 0, i = 0, result = fact(-1), result' = 0, i' = 1.
First conjunct of the goal (`result' = fact(i' - 1)`) reduces to
`0 = fact(0) = 1` via user_axiom_0; that's the contradiction.  The
second conjunct (`i' ≤ n + 1`) holds (1 ≤ 1).
-/
import SynthLean.Basic
open SynthLean

axiom fact : Int → Int
axiom user_axiom_0 : ((fact 0) = 1)
axiom user_axiom_1 : (∀ k : Int, ((k ≥ 0) → ((fact (k + 1)) = ((k + 1) * (fact k)))))

namespace SynthLean.VerifyTmp

theorem sc1_fallthrough_b2ecfd5b_is_invalid :
    ∃ (n result i result' i' : Int),
      (n ≥ 0) ∧
      (result = fact (i - 1)) ∧
      (i ≤ n + 1) ∧
      (i ≤ n) ∧
      (result' = result * i) ∧
      (i' = i + 1) ∧
      ¬ ((result' = fact (i' - 1)) ∧ (i' ≤ n + 1)) := by
  refine ⟨0, fact (-1), 0, 0, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl _              -- 0 ≥ 0
  · norm_num                     -- fact(-1) = fact(0 - 1)
  · decide                       -- 0 ≤ 0 + 1
  · exact le_refl _              -- 0 ≤ 0
  · ring                         -- 0 = fact(-1) * 0
  · rfl                          -- 1 = 0 + 1
  · intro ⟨h, _⟩
    rw [show ((1 : Int) - 1) = 0 from by ring] at h
    rw [user_axiom_0] at h
    exact absurd h (by decide)

end SynthLean.VerifyTmp
