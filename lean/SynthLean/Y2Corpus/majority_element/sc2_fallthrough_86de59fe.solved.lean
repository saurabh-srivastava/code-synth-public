/-
majority_element odd-branch (cnt = 0 → adopt A[i]) inductive,
τ subset = { i ≤ n, cnt ≥ 0, inv }.

Easy conjuncts handled inline (omega / direct).  The ∀v Boyer-Moore
inductive step uses the `bm_inv_preserve_b0` helper
axiom (see sc2_fallthrough_0f6231b2.solved.lean for full
documentation of why a helper is needed).
-/
import SynthLean.Core
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

private axiom bm_inv_preserve_b0
    (A : Int → Int) (n i candidate : Int)
    (h_pre : (n ≥ 1) ∧ (∃ v : Int, count_eq A n v > n / 2))
    (h_inv : ∀ v : Int, 0 + count_eq A i candidate ≥ count_eq A i v)
    (h_guard : i < n) :
    ∀ v : Int, 1 + count_eq A (i + 1) (A i) ≥ count_eq A (i + 1) v

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough
    (n candidate i cnt : Int)
    (A : Int → Int)
    (candidate' i' cnt' : Int)
    (h_pre : ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))))
    (h_tau_0 : (i ≤ n))
    (h_tau_1 : (cnt ≥ 0))
    (h_tau_2 : (∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v))))
    (h_guard : ((i < n) ∧ (cnt = 0)))
    (h_trans_candidate : candidate' = (A i))
    (h_trans_cnt : cnt' = 1)
    (h_trans_i : i' = (i + 1)) :
    ((i' ≤ n)) ∧ ((cnt' ≥ 0)) ∧ ((∀ v : Int, ((cnt' + (count_eq A i' candidate')) ≥ (count_eq A i' v)))) := by
    obtain ⟨h_lt, h_cnt0⟩ := h_guard
    refine ⟨?_, ?_, ?_⟩
    · rw [h_trans_i]; omega
    · rw [h_trans_cnt]; omega
    · intro v
      rw [h_trans_cnt, h_trans_i, h_trans_candidate]
      have h_inv0 : ∀ w : Int, 0 + count_eq A i candidate ≥ count_eq A i w := by
        intro w; have := h_tau_2 w; rw [h_cnt0] at this; exact this
      exact bm_inv_preserve_b0 A n i candidate h_pre h_inv0 h_lt v

end SynthLean.VerifyTmp
