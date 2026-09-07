/-
Companion to `sc1_fallthrough_class_3.failed.lean`.

VERDICT: genuinely INVALID — same root cause as classes 0, 1, 2.
This is the largest sc1 subset (still missing `i ≥ 1`).  All
preservation conjuncts in the goal hold at the counterexample;
only the recurrence conjunct fails.

Counterexample: n = 0, i = 0, result = fact(-1), result' = 0, i' = 1.
First conjunct of the goal (`result' = fact(i' - 1)`) reduces to
`0 = 1` via user_axiom_0; preservation conjuncts (`i' ≤ n + 1`,
`n ≥ 0`) hold trivially.
-/
import SynthLean.Basic
open SynthLean

axiom fact : Int → Int
axiom user_axiom_0 : ((fact 0) = 1)
axiom user_axiom_1 : (∀ k : Int, ((k ≥ 0) → ((fact (k + 1)) = ((k + 1) * (fact k)))))

namespace SynthLean.VerifyTmp

theorem sc1_fallthrough_6e6ef5b3_is_invalid :
    ∃ (n result i result' i' : Int),
      (n ≥ 0) ∧
      (result = fact (i - 1)) ∧
      (i ≤ n + 1) ∧
      (n ≥ 0) ∧
      (i ≤ n) ∧
      (result' = result * i) ∧
      (i' = i + 1) ∧
      ¬ ((result' = fact (i' - 1)) ∧ (i' ≤ n + 1) ∧ (n ≥ 0)) := by
  refine ⟨0, fact (-1), 0, 0, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl _              -- 0 ≥ 0
  · norm_num                     -- fact(-1) = fact(0 - 1)
  · decide                       -- 0 ≤ 0 + 1
  · exact le_refl _              -- 0 ≥ 0
  · exact le_refl _              -- 0 ≤ 0
  · ring                         -- 0 = fact(-1) * 0
  · rfl                          -- 1 = 0 + 1
  · intro ⟨h, _, _⟩
    rw [show ((1 : Int) - 1) = 0 from by ring] at h
    rw [user_axiom_0] at h
    exact absurd h (by decide)

end SynthLean.VerifyTmp
