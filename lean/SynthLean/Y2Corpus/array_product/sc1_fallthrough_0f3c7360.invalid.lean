/-
Companion to `sc1_fallthrough_class_0.failed.lean`.

VERDICT: genuinely INVALID.  Same shape as `Y2Corpus/factorial/sc1*`
— a UF recurrence with a nonnegativity precondition that the chosen
τ subset omits.

Chosen τ subset:
  - p = prod(A, i)
  - n ≥ 0 (redundant with h_pre)

Missing τ atom:
  - 0 ≤ i  (precondition of user_axiom_1).

Counterexample: pick n = 0, i = -1.  Then h_guard `i < n` holds
(-1 < 0), but the recurrence cannot fire (i is below the axiom's
domain).  Concretely: choose A such that A(-1) = 0, then
p' = p * A(-1) = 0, but the goal asks p' = prod(A, 0) = 1 via
user_axiom_0.  Contradiction.
-/
import SynthLean.Basic
open SynthLean

axiom prod : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((prod A 0) = 1)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ k : Int, ((k ≥ 0) → ((prod A (k + 1)) = ((prod A k) * (A k)))))

namespace SynthLean.VerifyTmp

theorem sc1_fallthrough_0f3c7360_is_invalid :
    ∃ (n p i p' i' : Int) (A : Int → Int),
      (n ≥ 0) ∧
      (p = prod A i) ∧
      (n ≥ 0) ∧
      (i < n) ∧
      (p' = p * A i) ∧
      (i' = i + 1) ∧
      ¬ ((p' = prod A i') ∧ (n ≥ 0)) := by
  -- Witness: n = 0, i = -1, A = (fun _ => 0).  Then p = prod A (-1)
  -- and p' = prod A (-1) * 0 = 0, but prod A 0 = 1.
  refine ⟨0, prod (fun _ => 0) (-1), -1, 0, 0, (fun _ => 0),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl _              -- 0 ≥ 0
  · rfl                          -- prod A (-1) = prod A (-1)
  · exact le_refl _              -- 0 ≥ 0
  · decide                       -- -1 < 0
  · ring                         -- 0 = prod A (-1) * 0
  · decide                       -- 0 = -1 + 1
  · intro ⟨h, _⟩
    rw [user_axiom_0] at h
    -- h : (0 : Int) = 1
    exact absurd h (by decide)

end SynthLean.VerifyTmp
