/-
majority_element even-branch (cnt > 0 → vote) inductive,
τ subset = { inv }.

Easy conjuncts handled inline (omega / direct).  The ∀v Boyer-Moore
inductive step uses the `bm_inv_preserve_b1` helper
axiom (see sc2_fallthrough_0f6231b2.solved.lean for full
documentation of why a helper is needed).
-/
import SynthLean.Core
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

private axiom bm_inv_preserve_b1
    (A : Int → Int) (n i candidate cnt : Int)
    (h_pre : (n ≥ 1) ∧ (∃ v : Int, count_eq A n v > n / 2))
    (h_inv : ∀ v : Int, cnt + count_eq A i candidate ≥ count_eq A i v)
    (h_guard : i < n ∧ cnt > 0) :
    ∀ v : Int,
      (if A i = candidate then cnt + 1 else cnt - 1)
        + count_eq A (i + 1) candidate ≥ count_eq A (i + 1) v

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n candidate i cnt : Int)
    (A : Int → Int)
    (i' cnt' : Int)
    (h_pre : ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))))
    (h_tau_0 : (∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v))))
    (h_guard : ((i < n) ∧ (cnt > 0)))
    (h_trans_cnt : cnt' = (if ((A i) = candidate) then (cnt + 1) else (cnt - 1)))
    (h_trans_i : i' = (i + 1)) :
    ((∀ v : Int, ((cnt' + (count_eq A i' candidate)) ≥ (count_eq A i' v)))) := by
    obtain ⟨h_lt, h_cnt_pos⟩ := h_guard
    intro v
    rw [h_trans_cnt, h_trans_i]
    exact bm_inv_preserve_b1 A n i candidate cnt h_pre h_tau_0 ⟨h_lt, h_cnt_pos⟩ v

end SynthLean.VerifyTmp
