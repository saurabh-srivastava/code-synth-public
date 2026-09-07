/-
verina_basic_23 (differenceMinMax) — loop inductive (safety) @ L0.

Preserve minVal=arrmin(A,i), maxVal=arrmax(A,i) across the body.
The conditional store update matches the fold step recurrence verbatim:
rewrite arrmin(A,i+1) via user_axiom_1 (k=i, i>=0 from h_tau_2), fold
the invariant minVal=arrmin(A,i) back in, then discharge with the
transition hypothesis.  Symmetric for max via user_axiom_3.
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
theorem sc1_fallthrough
    (n result minVal maxVal i : Int)
    (A : Int → Int)
    (minVal' maxVal' i' : Int)
    (h_pre : (n ≥ 1))
    (h_tau_0 : (minVal = (arrmin A i)))
    (h_tau_1 : (maxVal = (arrmax A i)))
    (h_tau_2 : (0 ≤ i))
    (h_tau_3 : (i ≤ n))
    (h_guard : (i < n))
    (h_trans_minVal : minVal' = (if ((A i) < minVal) then (A i) else minVal))
    (h_trans_maxVal : maxVal' = (if ((A i) > maxVal) then (A i) else maxVal))
    (h_trans_i : i' = (i + 1)) :
    ((minVal' = (arrmin A i'))) ∧ ((maxVal' = (arrmax A i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  subst h_trans_i
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmin : arrmin A (i + 1)
        = if A i < arrmin A i then A i else arrmin A i :=
      user_axiom_1 A i (by omega)
    rw [hmin, ← h_tau_0]; exact h_trans_minVal
  · have hmax : arrmax A (i + 1)
        = if A i > arrmax A i then A i else arrmax A i :=
      user_axiom_3 A i (by omega)
    rw [hmax, ← h_tau_1]; exact h_trans_maxVal
  · omega
  · omega

end SynthLean.VerifyTmp
