/-
Companion to `sc1_fallthrough_9219e4b3.failed.lean`.

VERDICT: PROVABLE — coverage proof `cnt = 0 ∨ cnt > 0` follows
from the bm_inv hypothesis by specializing v = candidate:
  cnt + count_eq A i candidate ≥ count_eq A i candidate
⇒ cnt ≥ 0
⇒ cnt = 0 ∨ cnt > 0.

The generic tactic chain didn't discover this specialization
(omega / nlinarith don't quantifier-instantiate; aesop / decide
don't see the pattern).  Hand-written shim citing bm_inv via
h_tau_0.
-/
import SynthLean.Basic
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n candidate i cnt : Int)
    (A : Int → Int)
    (h_pre : ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))))
    (h_tau_0 : (∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v))))
    (h_g_loop : (i < n)) :
    ((cnt = 0)) ∨ ((cnt > 0)) := by
  have h_bm := h_tau_0 candidate
  -- h_bm : cnt + count_eq A i candidate ≥ count_eq A i candidate
  have h_cnt_nn : cnt ≥ 0 := by linarith
  omega

end SynthLean.VerifyTmp
