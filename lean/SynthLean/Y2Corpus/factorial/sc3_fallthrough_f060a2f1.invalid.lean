/-
Companion to `sc3_fallthrough_class_0.failed.lean`.

VERDICT: genuinely INVALID — different shape than the sc1 family.
This is a ranking-LB obligation with empty τ; the goal `(n + 1) - i ≥ 0`
must follow from Pre alone (n ≥ 0).  But i is unconstrained — it
could be arbitrarily large.

Counterexample: n = 0, i = 2.  h_pre (n ≥ 0) holds, but (n + 1) - i
= 1 - 2 = -1 < 0.  No axiom about `fact` is needed for this
counterexample.
-/
import SynthLean.Basic
open SynthLean

axiom fact : Int → Int
axiom user_axiom_0 : ((fact 0) = 1)
axiom user_axiom_1 : (∀ k : Int, ((k ≥ 0) → ((fact (k + 1)) = ((k + 1) * (fact k)))))

namespace SynthLean.VerifyTmp

theorem sc3_fallthrough_f060a2f1_is_invalid :
    ∃ (n result i : Int),
      (n ≥ 0) ∧
      ¬ ((n + 1) - i ≥ 0) := by
  refine ⟨0, 0, 2, ?_, ?_⟩
  · exact le_refl _              -- 0 ≥ 0
  · decide                       -- ¬ (1 - 2 ≥ 0)

end SynthLean.VerifyTmp
