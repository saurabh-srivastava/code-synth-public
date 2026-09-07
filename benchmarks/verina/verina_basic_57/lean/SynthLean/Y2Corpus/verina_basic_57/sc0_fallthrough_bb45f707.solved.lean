/-
verina_basic_57 (CountLessThan) — entry-bundle obligation (sc0).
Init: c := 0, i := 0.  Chosen τ = {c = count_less(A,threshold,i),
0 ≤ i, i ≤ n}.  The UF-application conjunct 0 = count_less(A,
threshold,0) is the base axiom read symmetrically (REC 11.7.A
sc0 UF cliff); the two bounds are arithmetic.
-/
import SynthLean.Core
open SynthLean

axiom count_less : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (threshold : Int), ((count_less A threshold 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (threshold : Int),
  (∀ (k : Int), (((k ≥ 0) ∧ ((A k) < threshold)) →
    ((count_less A threshold (k + 1)) = ((count_less A threshold k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (threshold : Int),
  (∀ (k : Int), (((k ≥ 0) ∧ ((A k) ≥ threshold)) →
    ((count_less A threshold (k + 1)) = (count_less A threshold k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc0_fallthrough
    (n threshold c i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_init_c : c' = 0)
    (h_init_i : i' = 0) :
    ((c' = (count_less A threshold i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  subst_eqs
  refine ⟨?_, ?_, ?_⟩
  · exact (user_axiom_0 A threshold).symm
  · omega
  · omega

end SynthLean.VerifyTmp
