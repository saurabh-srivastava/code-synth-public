-- Curated companion for verina_basic_48 (isPerfectSquare), obligation
-- sc4 = safety-bundle-post on loop L0 (full τ = {r*r ≤ n, r ≥ 0}).
--
-- Discharges the postcondition biconditional
--     (result = 1)  ↔  ∃ i ≥ 0, i*i = n
-- at loop exit, where the loop established the floor-sqrt bracket
--     r*r ≤ n < (r+1)*(r+1),   r ≥ 0
-- and B2 set  result := if r*r = n then 1 else 0.
--
-- Forward: result = 1 forces the `then` branch, so r*r = n; witness i := r.
-- Backward: from a witness i ≥ 0 with i*i = n we get
--     r*r ≤ i*i < (r+1)*(r+1);
--   square-monotonicity on the non-negative integers pins i = r
--   (r ≤ i and i ≤ r), hence r*r = n, so result = 1.
--
-- No uninterpreted functions, no trusted axioms — the monotonicity is
-- proved from first principles.  Core-only (no mathlib): the two
-- monotonicity steps use Lean-core `Int.mul_le_mul_of_nonneg_*` /
-- `Int.mul_lt_mul_of_pos_right`, and `omega` abstracts the products as
-- atoms to close each contradiction.  Kept off `SynthLean.Basic`
-- deliberately so the cache-consult type-check (~2s) fits the solver's
-- adaptive per-class Lean budget (REC 11.8 / F16); the mathlib
-- `nlinarith` version type-checked but at ~11s blew the reduced budget.
import SynthLean.Core
open SynthLean

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc4_fallthrough
    (n result r : Int)
    (result' r' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : ((r' * r') ≤ n))
    (h_tau_1 : (r' ≥ 0))
    (h_not_g : ¬ ((((r' + 1) * (r' + 1)) ≤ n)))
    (h_skip_result : result' = (if ((r' * r') = n) then 1 else 0)) :
    (((result' = 1) → (∃ (i : Int), ((i ≥ 0) ∧ ((i * i) = n)))) ∧ ((∃ (i : Int), ((i ≥ 0) ∧ ((i * i) = n))) → (result' = 1))) := by
  have hng : n < (r' + 1) * (r' + 1) := by omega
  constructor
  · -- forward: result' = 1 forces the `then` branch (r'*r' = n); witness r'
    intro hres
    by_cases hsq : r' * r' = n
    · exact ⟨r', h_tau_1, hsq⟩
    · exfalso
      rw [if_neg hsq] at h_skip_result
      omega
  · -- backward: a witness i ≥ 0 with i*i = n pins i = r', so r'*r' = n
    rintro ⟨i, hi_nonneg, hi_sq⟩
    have hle : r' * r' ≤ i * i := by rw [hi_sq]; exact h_tau_0
    have hlt : i * i < (r' + 1) * (r' + 1) := by rw [hi_sq]; exact hng
    -- r' ≤ i  from  r'*r' ≤ i*i  (both nonneg)
    have hri : r' ≤ i := by
      by_cases h : r' ≤ i
      · exact h
      · exfalso
        have hlt' : i < r' := by omega
        have hile : i ≤ r' := by omega
        have hr_pos : 0 < r' := by omega
        have a1 : i * i ≤ i * r' := Int.mul_le_mul_of_nonneg_left hile hi_nonneg
        have a2 : i * r' < r' * r' := Int.mul_lt_mul_of_pos_right hlt' hr_pos
        omega
    -- i ≤ r'  from  i*i < (r'+1)*(r'+1)  (i and r'+1 nonneg)
    have hir : i ≤ r' := by
      by_cases h : i ≤ r'
      · exact h
      · exfalso
        have hb : r' + 1 ≤ i := by omega
        have hb0 : (0:Int) ≤ r' + 1 := by omega
        have a1 : (r' + 1) * (r' + 1) ≤ (r' + 1) * i := Int.mul_le_mul_of_nonneg_left hb hb0
        have a2 : (r' + 1) * i ≤ i * i := Int.mul_le_mul_of_nonneg_right hb hi_nonneg
        omega
    have heq : i = r' := by omega
    have hsq : r' * r' = n := by rw [heq] at hi_sq; exact hi_sq
    rw [if_pos hsq] at h_skip_result
    exact h_skip_result
end SynthLean.VerifyTmp
