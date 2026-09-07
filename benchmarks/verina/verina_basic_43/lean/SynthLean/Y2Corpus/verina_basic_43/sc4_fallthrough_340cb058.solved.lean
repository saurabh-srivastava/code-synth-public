-- Curated companion for verina_basic_43 (sumOfFourthPowerOfOddNumbers).
-- Obligation: loop-exit (safety-bundle-post) for the τ subset
--   {main closed-form invariant, i' ≤ n}.
-- From h_tau_1 (i' ≤ n) and h_not_g (¬ i' < n, i.e. n ≤ i') we get
-- i' = n by omega; substituting into the main invariant h_tau_0 gives
-- the postcondition verbatim.  The generic tactic chain (omega / nlinarith
-- / aesop) cannot do the i' = n substitution into the degree-5 polynomial,
-- so this hand proof is required.
import SynthLean.Basic
open SynthLean

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc4_fallthrough
    (n s i : Int)
    (s' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : ((15 * s') = ((i' * ((2 * i') + 1)) * (((7 + (((24 * i') * i') * i')) - ((12 * i') * i')) - (14 * i')))))
    (h_tau_1 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    ((15 * s') = ((n * ((2 * n) + 1)) * (((7 + (((24 * n) * n) * n)) - ((12 * n) * n)) - (14 * n)))) := by
  have hin : i' = n := by omega
  subst hin
  exact h_tau_0
end SynthLean.VerifyTmp
