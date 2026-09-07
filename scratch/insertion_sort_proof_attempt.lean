/-
Scratch: insertion_sort_l1_body_inductive_chain Tier-1 proof.

Goal: prove A[0..i_s2+1) sorted, given A[0..j_s2) sorted +
A[j_s2..i_s2] sorted + wall LB (A[j_s2-1] ≤ A[k] for k > j_s2-1)
+ ¬g_L1 (j_s2 = 0 OR A[j_s2-1] ≤ A[j_s2]).
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.insertion_sort.Helpers
open SynthLean

theorem insertion_sort_attempt :
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
  intros
  subst_eqs
  rename_i h_n_s0_ge0 h_i_s0_ge0 h_i_s0_le_n _ _ h_i_s0_lt_n
           h_j_s2_ge0 h_j_s2_le_i h_i_s2_lt_n h_n_s2_ge0
           h_sorted_pre h_sorted_suf h_wall h_notg
  refine ⟨?_, ?_, h_n_s2_ge0, ?_⟩
  · omega
  · omega
  -- A[0..i_s2+1) sorted.
  intro p q ⟨h_p0, h_p_le_q, h_q_lt⟩
  -- Cases on j_s2 = 0 vs j_s2 > 0.
  by_cases hj0 : j_s2 = 0
  · -- j_s2 = 0: sorted-suffix covers everything (j_s2 ≤ p).
    have h_p_ge : j_s2 ≤ p := by omega
    exact h_sorted_suf p q ⟨h_p_ge, h_p_le_q, by omega⟩
  · -- j_s2 > 0.  Then h_notg gives A[j_s2-1] ≤ A[j_s2].
    have h_j_pos : j_s2 > 0 := by omega
    have h_bridge : A_s2 (j_s2 - 1) ≤ A_s2 j_s2 := by
      by_contra h_gt
      apply h_notg
      exact ⟨h_j_pos, by linarith⟩
    -- Now case-split p < j_s2 vs p ≥ j_s2.
    by_cases hp : p < j_s2
    · -- p < j_s2.  Case split q.
      by_cases hq : q < j_s2
      · -- p ≤ q < j_s2: sorted-prefix.
        exact h_sorted_pre p q ⟨h_p0, h_p_le_q, hq⟩
      · -- p < j_s2 ≤ q ≤ i_s2.
        -- A[p] ≤ A[j_s2-1] (sorted-prefix), A[j_s2-1] ≤ A[q] (wall).
        have h_p_le : A_s2 p ≤ A_s2 (j_s2 - 1) :=
          h_sorted_pre p (j_s2 - 1) ⟨h_p0, by omega, by omega⟩
        by_cases hq_eq_j : q = j_s2
        · -- q = j_s2: A[j_s2-1] ≤ A[j_s2] (h_bridge).
          subst hq_eq_j; linarith
        · have h_q_gt : j_s2 < q := by omega
          have h_q_le : A_s2 (j_s2 - 1) ≤ A_s2 q :=
            h_wall q ⟨h_j_pos, h_q_gt, by omega⟩
          linarith
    · -- p ≥ j_s2: sorted-suffix.
      exact h_sorted_suf p q ⟨by omega, h_p_le_q, by omega⟩
