/-
Companion to `sc6_fallthrough_1753ee5b.failed.lean`.

VERDICT: genuinely INVALID — empty-τ ranking-lb for kadane.
The obligation requires `n - i ≥ 0` to follow from `h_pre = n ≥ 1`
alone (no τ atoms in scope).  Nothing constrains `i` from above
without the `i ≤ n` τ atom.

Counterexample: n = 1, i = 2, best = 0, cur = 0, A = const 0.
Pre holds (n = 1 ≥ 1).  Goal n - i = -1 < 0.

The synthesizer's monotonicity fast-path correctly enumerates
this hardest case (ANT-only τ → empty subset hardest), Lean
omega correctly fails to prove without the τ premise, and the
class is rejected.  The non-empty subsets including `i ≤ n`
(atom 1) DO validate.
-/
import SynthLean.Basic
open SynthLean

axiom sum_range : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ p : Int, ((sum_range A p p) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ p q : Int, ((p ≤ q) → ((sum_range A p (q + 1)) = ((sum_range A p q) + (A q)))))

namespace SynthLean.VerifyTmp

theorem sc6_fallthrough_1753ee5b_is_invalid :
    ∃ (n best i cur : Int) (A : Int → Int),
      (n ≥ 1) ∧ ¬ ((n - i) ≥ 0) := by
  refine ⟨1, 0, 2, 0, fun _ => 0, ?_, ?_⟩
  · exact le_refl 1
  · decide

end SynthLean.VerifyTmp
