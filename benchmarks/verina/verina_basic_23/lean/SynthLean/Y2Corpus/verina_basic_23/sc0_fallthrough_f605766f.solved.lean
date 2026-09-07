/-
verina_basic_23 (differenceMinMax) — entry-bundle (safety-bundle-entry) @ L0.

At entry minVal'=maxVal'=A[0], i'=0.  arrmin/arrmax at 0 are
A[0] by the fold base axioms (user_axiom_0 / user_axiom_2); bounds by omega.
-/
import SynthLean.Core
open SynthLean

axiom arrmin : (Int → Int) → Int → Int
axiom arrmax : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((arrmin A 0) = (A 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ (k : Int), ((k ≥ 0) → ((arrmin A (k + 1)) = (if ((A k) < (arrmin A k)) then (A k) else (arrmin A k)))))
axiom user_axiom_2 : ∀ (A : Int → Int), ((arrmax A 0) = (A 0))
axiom user_axiom_3 : ∀ (A : Int → Int), (∀ (k : Int), ((k ≥ 0) → ((arrmax A (k + 1)) = (if ((A k) > (arrmax A k)) then (A k) else (arrmax A k)))))
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc0_fallthrough
    (n result minVal maxVal i : Int)
    (A : Int → Int)
    (minVal' maxVal' i' : Int)
    (h_pre : (n ≥ 1))
    (h_init_minVal : minVal' = (A 0))
    (h_init_maxVal : maxVal' = (A 0))
    (h_init_i : i' = 0) :
    ((minVal' = (arrmin A i'))) ∧ ((maxVal' = (arrmax A i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  subst h_init_minVal h_init_maxVal h_init_i
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (user_axiom_0 A).symm
  · exact (user_axiom_2 A).symm
  · omega
  · omega

end SynthLean.VerifyTmp
