/-
Companion to `sc1_fallthrough_class_0.failed.lean`.

VERDICT: genuinely INVALID.  The synthesizer correctly rejects this
attribute-class subset.  NEGATIVE training example for the Phase Y.2
driver-LLM: when seeing this obligation shape, the right answer is
"the chosen τ is insufficient — request more atoms" rather than
attempting a proof.

Chosen τ subset:
  - result = fact(i - 1)

Missing τ atom:
  - i ≥ 1   (required as the precondition of user_axiom_1).

Counterexample:
  - n = 0, i = 0, result = fact(-1), result' = 0, i' = 1.
  - All hypotheses hold; conclusion `result' = fact(i' - 1) = fact(0)`
    reduces to `0 = 1` via user_axiom_0.
-/
import SynthLean.Basic
open SynthLean

axiom fact : Int → Int
axiom user_axiom_0 : ((fact 0) = 1)
axiom user_axiom_1 : (∀ k : Int, ((k ≥ 0) → ((fact (k + 1)) = ((k + 1) * (fact k)))))

namespace SynthLean.VerifyTmp

theorem sc1_fallthrough_ff5841b7_is_invalid :
    ∃ (n result i result' i' : Int),
      (n ≥ 0) ∧
      (result = fact (i - 1)) ∧
      (i ≤ n) ∧
      (result' = result * i) ∧
      (i' = i + 1) ∧
      ¬ (result' = fact (i' - 1)) := by
  refine ⟨0, fact (-1), 0, 0, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl _              -- 0 ≥ 0
  · norm_num                     -- fact(-1) = fact(0 - 1)
  · exact le_refl _              -- 0 ≤ 0
  · ring                         -- 0 = fact(-1) * 0
  · rfl                          -- 1 = 0 + 1
  -- Goal: ¬ (0 = fact (1 - 1))
  · intro h
    rw [show ((1 : Int) - 1) = 0 from by ring] at h
    rw [user_axiom_0] at h
    -- h : (0 : Int) = 1
    exact absurd h (by decide)

end SynthLean.VerifyTmp
