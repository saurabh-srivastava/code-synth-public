/-
verina_basic_23 (differenceMinMax) — chain-bundle post (safety-bundle-post) @ L0.

At loop exit i'=n (from 0<=i', i'<=n, not(i'<n)).  Then
minVal'=arrmin(A,n), maxVal'=arrmax(A,n), result'=maxVal'-minVal', so
result'+arrmin(A,n)=arrmax(A,n) is linear (omega over the UF atoms).
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
theorem sc4_fallthrough
    (n result minVal maxVal i : Int)
    (A : Int → Int)
    (result' minVal' maxVal' i' : Int)
    (h_pre : (n ≥ 1))
    (h_tau_0 : (minVal' = (arrmin A i')))
    (h_tau_1 : (maxVal' = (arrmax A i')))
    (h_tau_2 : (0 ≤ i'))
    (h_tau_3 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n)))
    (h_skip_result : result' = (maxVal' - minVal')) :
    ((result' + (arrmin A n)) = (arrmax A n)) := by
  have hi : i' = n := by omega
  subst hi
  omega

end SynthLean.VerifyTmp
