/-
Companion to `sc6_fallthrough_78d74491.failed.lean`.

VERDICT: genuinely INVALID — empty-τ ranking-lb for modular_exp.
The obligation requires `exp ≥ 0` to follow from `h_pre` alone
(no τ atoms in scope).  But `h_pre = (e ≥ 0 ∧ m ≥ 1)` says
nothing about the loop variable `exp`; nothing prevents
`exp = -1`.

Counterexample: e = 0, m = 1, b = 0, result = 0, base = 0,
exp = -1.  Pre holds (0 ≥ 0 ∧ 1 ≥ 1).  Goal exp ≥ 0 is false.

The synthesizer's monotonicity fast-path correctly enumerates
this hardest case (ANT-only τ → empty subset hardest), Lean
omega correctly fails to prove without the τ premise, and the
class is rejected.  The non-empty subsets including `exp ≥ 0`
(atom 0) DO validate.
-/
import SynthLean.Basic
open SynthLean

axiom pow : Int → Int → Int
axiom user_axiom_0 : (∀ x : Int, ((pow x 0) = 1))
axiom user_axiom_1 : (∀ x k : Int, ((k ≥ 0) → ((pow x (k + 1)) = (x * (pow x k)))))
axiom user_axiom_2 : (∀ x k : Int, ((k ≥ 0) → ((pow x (2 * k)) = (pow (x * x) k))))
axiom user_axiom_3 : (∀ x y mm : Int, ((mm ≥ 1) → (((x * y) % mm) = (((x % mm) * (y % mm)) % mm))))

namespace SynthLean.VerifyTmp

theorem sc6_fallthrough_78d74491_is_invalid :
    ∃ b e m result base exp : Int,
      ((e ≥ 0) ∧ (m ≥ 1)) ∧ ¬ (exp ≥ 0) := by
  refine ⟨0, 0, 1, 0, 0, -1, ⟨?_, ?_⟩, ?_⟩
  · exact le_refl 0
  · exact le_refl 1
  · decide

end SynthLean.VerifyTmp
