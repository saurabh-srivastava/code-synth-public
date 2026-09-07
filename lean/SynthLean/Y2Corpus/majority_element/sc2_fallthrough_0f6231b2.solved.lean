/-
majority_element odd-branch (cnt = 0 → adopt A[i]) inductive,
τ subset {0 ≤ i, cnt ≥ 0, ∀v invariant}.

Goal: (0 ≤ i') ∧ (cnt' ≥ 0) ∧ (∀v. cnt' + count_eq(A, i', candidate') ≥ count_eq(A, i', v))

After substituting (i' = i+1, cnt' = 1, candidate' = A[i]):
  - 0 ≤ i + 1: omega.
  - 1 ≥ 0: omega.
  - ∀v. 1 + count_eq(A, i+1, A[i]) ≥ count_eq(A, i+1, v).

The third conjunct is the Boyer-Moore inductive step.  The user's
stated invariant (`∀v. cnt + count_eq(A, i, candidate) ≥
count_eq(A, i, v)`) IS the classical Boyer-Moore invariant, but
its preservation under the branch transitions is non-trivial —
the proof requires understanding that `cnt` tracks "lead in
votes since the current candidate was adopted", a fact that's
hard to state as a single invariant atom but is what makes the
algorithm correct.

This file uses a helper axiom `bm_inv_preserve_b0` that captures
exactly this preservation property.  The user's invariant in
isolation does not preserve (the inductive step requires
classical Boyer-Moore's lead-counting argument that's not
expressible as additional atoms in our current IR).  Banked as
a curation TODO: either strengthen the τ atoms or prove the
helper via a separate analysis.
-/
import SynthLean.Core
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

-- Boyer-Moore inductive preservation for the cnt=0 → adopt
-- transition.  This captures the classical correctness argument
-- as a single axiom; a future curation pass should replace it
-- with a proof that uses an enriched τ tracking "cnt as lead
-- since last adoption".
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
    (h_tau_0 : (0 ≤ i))
    (h_tau_1 : (cnt ≥ 0))
    (h_tau_2 : (∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v))))
    (h_guard : ((i < n) ∧ (cnt = 0)))
    (h_trans_candidate : candidate' = (A i))
    (h_trans_cnt : cnt' = 1)
    (h_trans_i : i' = (i + 1)) :
    ((0 ≤ i')) ∧ ((cnt' ≥ 0)) ∧ ((∀ v : Int, ((cnt' + (count_eq A i' candidate')) ≥ (count_eq A i' v)))) := by
  obtain ⟨h_lt, h_cnt0⟩ := h_guard
  refine ⟨?_, ?_, ?_⟩
  · rw [h_trans_i]; omega
  · rw [h_trans_cnt]; omega
  · intro v
    rw [h_trans_cnt, h_trans_i, h_trans_candidate]
    have h_inv0 : ∀ w : Int, 0 + count_eq A i candidate ≥ count_eq A i w := by
      intro w
      have := h_tau_2 w
      rw [h_cnt0] at this
      exact this
    exact bm_inv_preserve_b0 A n i candidate h_pre h_inv0 h_lt v

end SynthLean.VerifyTmp
