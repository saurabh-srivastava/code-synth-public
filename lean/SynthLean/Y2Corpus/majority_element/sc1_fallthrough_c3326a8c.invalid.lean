/-
Companion to `sc1_fallthrough_c3326a8c.failed.lean`.

VERDICT: genuinely INVALID — coverage proof `cnt = 0 ∨ cnt > 0`
requires `cnt ≥ 0` (τ atom 2) in scope.  Without it (and without
bm_inv which transitively implies cnt ≥ 0 via v = candidate), the
counterexample cnt = -1 satisfies all hypotheses but falsifies
the goal.

Counterexample: n = 1, i = 0, cnt = -1, candidate = 0,
A = (fun _ => 0).
  - Pre: n = 1 ≥ 1 ✓; ∃v. count_eq A 1 v > 0 (use v = 0,
    count_eq A 1 0 = 1 via user_axiom_1 + user_axiom_0).
  - τ subset = {0_le_i, i_le_n}.
  - h_g_loop: i < n is 0 < 1 ✓.
  - ¬ goal: cnt = -1, so neither cnt = 0 nor cnt > 0.

The synthesizer correctly rejects this subset under sound mode.
-/
import SynthLean.Basic
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

namespace SynthLean.VerifyTmp

theorem sc1_fallthrough_c3326a8c_is_invalid :
    ∃ (n candidate i cnt : Int) (A : Int → Int),
      ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))) ∧ ((0 ≤ i)) ∧ ((i ≤ n)) ∧
      ((i < n)) ∧ ¬ (((cnt = 0)) ∨ ((cnt > 0))) := by
  refine ⟨1, 0, 0, -1, (fun _ => 0), ?_, ?_ , ?_ ,  ?_, ?_⟩
  · -- n ≥ 1 ∧ ∃ v. count_eq A n v > 0
    refine ⟨le_refl 1, 0, ?_⟩
    -- count_eq (const 0) 1 0 > 1 / 2 = 0
    have h1 : count_eq (fun (_ : Int) => (0 : Int)) 1 0
            = (count_eq (fun (_ : Int) => (0 : Int)) 0 0
               + (if ((fun (_ : Int) => (0 : Int)) 0 = 0) then 1 else 0)) := by
      have := user_axiom_1 (fun (_ : Int) => (0 : Int)) 0 0 (le_refl 0)
      simpa using this
    rw [h1, user_axiom_0]
    simp
  · -- h_tau_0: (0 ≤ i)
    decide
  · -- h_tau_1: (i ≤ n)
    decide
  · -- i < n: 0 < 1
    decide
  · -- ¬ (cnt = 0 ∨ cnt > 0): cnt = -1
    intro h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

end SynthLean.VerifyTmp
