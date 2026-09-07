/-
SAMPLE Tier-3-helper shim for modular_exp's sc7 (bundle-post)
when τ has all 5 required atoms (exp_nn, m_ge_1, pow_inv, res_nn,
res_lt_m).

This file is a TEMPLATE — the actual sc7 dumps would have
real signature hashes (replace SAMPLE_FULL_TAU with the
content-hash from the dump).  Shown here to demonstrate the
Tier-3 helper pattern works.

The proof is a 5-line citation of post_from_inv from the
helpers file.  Compare to the Run 1 sc2 hand-curated proofs
(~60 lines each) — the Tier-3 approach moves the proof
content into the helper file once, and each shim becomes
mechanical.
-/
import SynthLean.Core
import SynthLean.Y2Corpus.modular_exponentiation.Helpers

open SynthLean
-- `pow` and the user_axiom_* are at the top level of the Helpers
-- file; they become available after the import.  No re-declaration
-- needed in the shim.

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc7_fallthrough
    (b e m result base exp : Int)
    (result' base' exp' : Int)
    (h_pre : ((e ≥ 0) ∧ (m ≥ 1)))
    (h_tau_0 : (exp' ≥ 0))
    (h_tau_1 : (m ≥ 1))
    (h_tau_2 : (((result' * (pow base' exp')) % m) = ((pow b e) % m)))
    (h_tau_3 : (result' ≥ 0))
    (h_tau_4 : (result' < m))
    (h_not_g : ¬ (exp' > 0)) :
    result' = ((pow b e) % m) := by
  exact SynthLean.ModExpHelpers.post_from_inv
    b e m result' base' exp'
    h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_not_g

end SynthLean.VerifyTmp
