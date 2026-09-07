/-
insertion_sort Tier-2 helper — for chain-aware bundle-post on
L1 (the outer loop's body inductive when nested chain-bundle
extension applies, task #167).

The sc5 obligation:
  Pre @ s0 + τ@L0 + g@L0 (the outer state)
  + B1 init (j := i) at s0→s1
  + L1 abstract τ + ¬g_L1 + frame at s1→s2
  + B5 (i := i + 1) at s2→s3
  ⇒ τ@L0 at s3

This is the body inductive of L0 (insertion sort's outer):
"if we entered the outer loop with prefix A[0..i_s0) sorted
and the inner loop completed (¬g_L1 means inserting element
reached its position), then the new prefix A[0..i_s0+1) is
sorted."

Banked as Tier-2 axiom; could be proved from the inner τ
invariants by case-split on j_s2 = 0 vs > 0, but the existing
helpers for FW / merge follow the same Tier-2 pattern.  Future
work: convert to a theorem.
-/
import SynthLean.Basic
open SynthLean

-- Tier-1: Insertion sort body — after L1 (inner-swap loop)
-- completes, prove A[0..i+1) sorted.  ¬g_L1 says j_s2 = 0 OR
-- A[j_s2-1] ≤ A[j_s2].  Case-split on j_s2 = 0:
--   - j_s2 = 0: sorted-suffix covers [0, i+1].
--   - j_s2 > 0 (with bridge A[j_s2-1] ≤ A[j_s2]):
--     - p < j_s2 ∧ q < j_s2: sorted-prefix.
--     - p < j_s2 ≤ q: sorted-prefix to j-1 + wall LB.
--     - p ≥ j_s2: sorted-suffix.
theorem insertion_sort_l1_body_inductive_chain :
    ∀ (n_s0 i_s0 j_s0 : Int)
      (A_s0 : Int → Int)
      (n_s1 i_s1 j_s1 : Int)
      (A_s1 : Int → Int)
      (n_s2 i_s2 j_s2 : Int)
      (A_s2 : Int → Int)
      (n_s3 i_s3 j_s3 : Int)
      (A_s3 : Int → Int),
    (n_s0 ≥ 0) →
    (0 ≤ i_s0) → (i_s0 ≤ n_s0) → (n_s0 ≥ 0) →
    (∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i_s0)) → ((A_s0 p) ≤ (A_s0 q)))) →
    (i_s0 < n_s0) →
    (j_s1 = i_s0) → (n_s1 = n_s0) → (i_s1 = i_s0) → (A_s1 = A_s0) →
    (0 ≤ j_s2) → (j_s2 ≤ i_s2) → (i_s2 < n_s2) → (n_s2 ≥ 0) →
    (∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < j_s2)) → ((A_s2 p) ≤ (A_s2 q)))) →
    (∀ p q : Int, (((j_s2 ≤ p) ∧ (p ≤ q) ∧ (q ≤ i_s2)) → ((A_s2 p) ≤ (A_s2 q)))) →
    (∀ k : Int, (((j_s2 > 0) ∧ (j_s2 < k) ∧ (k ≤ i_s2)) → ((A_s2 (j_s2 - 1)) ≤ (A_s2 k)))) →
    ¬ ((j_s2 > 0) ∧ ((A_s2 (j_s2 - 1)) > (A_s2 j_s2))) →
    (n_s2 = n_s1) → (i_s2 = i_s1) →
    (i_s3 = (i_s2 + 1)) → (n_s3 = n_s2) → (j_s3 = j_s2) → (A_s3 = A_s2) →
    ((0 ≤ i_s3) ∧ (i_s3 ≤ n_s3) ∧ (n_s3 ≥ 0) ∧
     (∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i_s3)) → ((A_s3 p) ≤ (A_s3 q))))) := by
  -- Name j_s2, A_s2 (positions 11, 12).  Only subst s1 vars (eliminated)
  -- and s3 i_s3 → i_s2 + 1.  Keep h_n3, h_j3, h_A3 as rewrites.
  intro _ _ _ _ _ _ _ _ _ _ j_s2 A_s2 _ _ _ _
  intro _ _ _ _ _ _
  intro h_jeq1 h_neq1 h_ieq1 h_Aeq1
  intro h_j_s2_ge h_j_s2_le_i h_i_s2_lt h_n_s2_ge
  intro h_sorted_pre h_sorted_suf h_wall h_notg
  intro h_n21 h_i21
  intro h_ieq3 h_n3 h_j3 h_A3
  subst h_jeq1 h_neq1 h_ieq1 h_Aeq1
  subst h_ieq3
  rw [h_n3, h_A3]
  refine ⟨?_, ?_, h_n_s2_ge, ?_⟩
  · omega
  · omega
  intro p q ⟨h_p0, h_p_le_q, h_q_lt⟩
  by_cases hj0 : j_s2 = 0
  · exact h_sorted_suf p q ⟨by omega, h_p_le_q, by omega⟩
  · have h_jpos : j_s2 > 0 := by omega
    have h_bridge : A_s2 (j_s2 - 1) ≤ A_s2 j_s2 := by
      by_contra h_gt; apply h_notg; exact ⟨h_jpos, by linarith⟩
    by_cases hp : p < j_s2
    · by_cases hq : q < j_s2
      · exact h_sorted_pre p q ⟨h_p0, h_p_le_q, hq⟩
      · have h_p_le_jm1 : A_s2 p ≤ A_s2 (j_s2 - 1) :=
          h_sorted_pre p (j_s2 - 1) ⟨h_p0, by omega, by omega⟩
        by_cases hqj : q = j_s2
        · subst hqj; linarith
        · have h_q_gt : j_s2 < q := by omega
          have h_jm1_le_q : A_s2 (j_s2 - 1) ≤ A_s2 q :=
            h_wall q ⟨h_jpos, h_q_gt, by omega⟩
          linarith
    · exact h_sorted_suf p q ⟨by omega, h_p_le_q, by omega⟩

namespace SynthLean.InsertionSortHelpers

-- Placeholder for future Tier-1 theorems.

end SynthLean.InsertionSortHelpers
