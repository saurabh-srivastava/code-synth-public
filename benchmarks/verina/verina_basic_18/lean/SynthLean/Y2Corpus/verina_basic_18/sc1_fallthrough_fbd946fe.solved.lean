/-
verina_basic_18 (sumOfDigits) loop-inductive obligation, full τ =
{ s + digitSum(m) = digitSum(n),  m ≥ 0 }.

Body: s' = s + m % 10,  m' = m / 10.  Guard m ≠ 0 with m ≥ 0 gives
m > 0.  Apply the multiplicative digit-peel axiom at q = m / 10,
r = m % 10 (its side conditions q ≥ 0, 0 ≤ r ≤ 9 discharge by omega),
then rewrite 10*(m/10) + m%10 = m to fold the peeled term back into
digitSum m and substitute into the invariant h_tau_0.
-/
import SynthLean.Core
open SynthLean

axiom digitSum : Int → Int
axiom user_axiom_0 : ((digitSum 0) = 0)
axiom user_axiom_1 : (∀ (q : Int) (r : Int), (((q ≥ 0) ∧ (0 ≤ r) ∧ (r ≤ 9)) → ((digitSum ((10 * q) + r)) = ((digitSum q) + r))))
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc1_fallthrough
    (n s m : Int)
    (s' m' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : ((s + (digitSum m)) = (digitSum n)))
    (h_tau_1 : (m ≥ 0))
    (h_guard : (m ≠ 0))
    (h_trans_s : s' = (s + (m % 10)))
    (h_trans_m : m' = (m / 10)) :
    (((s' + (digitSum m')) = (digitSum n))) ∧ ((m' ≥ 0)) := by
  subst h_trans_s h_trans_m
  refine ⟨?_, ?_⟩
  · -- s + m % 10 + digitSum (m / 10) = digitSum n
    have hq : m / 10 ≥ 0 := by omega
    have hr0 : 0 ≤ m % 10 := by omega
    have hr9 : m % 10 ≤ 9 := by omega
    have hsplit : (10 * (m / 10) + (m % 10)) = m := by omega
    have hax := user_axiom_1 (m / 10) (m % 10) ⟨hq, hr0, hr9⟩
    rw [hsplit] at hax
    -- hax : digitSum m = digitSum (m / 10) + m % 10
    rw [hax] at h_tau_0
    -- h_tau_0 : s + (digitSum (m / 10) + m % 10) = digitSum n
    omega
  · -- m / 10 ≥ 0
    omega
end SynthLean.VerifyTmp
