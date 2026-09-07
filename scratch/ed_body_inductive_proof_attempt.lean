/-
Scratch v2: simpler approach with subst_eqs.
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.edit_distance.Helpers
open SynthLean

theorem ed_l1_body_inductive_chain_attempt :
    ∀ (n_s0 m_s0 result_s0 i_s0 j_s0 : Int)
      (A_s0 B_s0 : Int → Int)
      (ed_s0 : Int → Int → Int)
      (n_s1 m_s1 result_s1 i_s1 j_s1 : Int)
      (A_s1 B_s1 : Int → Int)
      (ed_s1 : Int → Int → Int)
      (n_s2 m_s2 result_s2 i_s2 j_s2 : Int)
      (A_s2 B_s2 : Int → Int)
      (ed_s2 : Int → Int → Int)
      (n_s3 m_s3 result_s3 i_s3 j_s3 : Int)
      (A_s3 B_s3 : Int → Int)
      (ed_s3 : Int → Int → Int),
    ((n_s0 ≥ 0) ∧ (m_s0 ≥ 0)
       ∧ (∀ k : Int, (((0 ≤ k) ∧ (k ≤ n_s0)) → (((ed_s0 k) 0) = k)))
       ∧ (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m_s0)) → (((ed_s0 0) l) = l)))) →
    (1 ≤ i_s0) → (i_s0 ≤ (n_s0 + 1)) → (n_s0 ≥ 0) → (m_s0 ≥ 0) →
    (∀ p q : Int, (((0 ≤ p) ∧ (p < i_s0) ∧ (0 ≤ q) ∧ (q ≤ m_s0)) → (((ed_s0 p) q) = (edit_dist A_s0 p B_s0 q)))) →
    (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n_s0)) → (((ed_s0 p) 0) = p))) →
    (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m_s0)) → (((ed_s0 0) l) = l))) →
    (i_s0 ≤ n_s0) →
    (j_s1 = 1) → (n_s1 = n_s0) → (m_s1 = m_s0) → (result_s1 = result_s0) →
    (i_s1 = i_s0) → (A_s1 = A_s0) → (B_s1 = B_s0) → (ed_s1 = ed_s0) →
    (1 ≤ i_s2) → (i_s2 ≤ n_s2) → (1 ≤ j_s2) → (j_s2 ≤ (m_s2 + 1)) →
    (n_s2 ≥ 0) → (m_s2 ≥ 0) →
    (∀ p q : Int, (((0 ≤ p) ∧ (p < i_s2) ∧ (0 ≤ q) ∧ (q ≤ m_s2)) → (((ed_s2 p) q) = (edit_dist A_s2 p B_s2 q)))) →
    (∀ q : Int, (((0 ≤ q) ∧ (q < j_s2)) → (((ed_s2 i_s2) q) = (edit_dist A_s2 i_s2 B_s2 q)))) →
    (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n_s2)) → (((ed_s2 p) 0) = p))) →
    (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m_s2)) → (((ed_s2 0) l) = l))) →
    ¬ (j_s2 ≤ m_s2) →
    (n_s2 = n_s1) → (m_s2 = m_s1) → (result_s2 = result_s1) →
    (i_s2 = i_s1) → (A_s2 = A_s1) → (B_s2 = B_s1) →
    (i_s3 = (i_s2 + 1)) → (n_s3 = n_s2) → (m_s3 = m_s2) → (result_s3 = result_s2) →
    (j_s3 = j_s2) → (A_s3 = A_s2) → (B_s3 = B_s2) → (ed_s3 = ed_s2) →
    ((1 ≤ i_s3) ∧ (i_s3 ≤ (n_s3 + 1)) ∧ (n_s3 ≥ 0) ∧ (m_s3 ≥ 0) ∧
     (∀ p q : Int, (((0 ≤ p) ∧ (p < i_s3) ∧ (0 ≤ q) ∧ (q ≤ m_s3)) → (((ed_s3 p) q) = (edit_dist A_s3 p B_s3 q)))) ∧
     (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n_s3)) → (((ed_s3 p) 0) = p))) ∧
     (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m_s3)) → (((ed_s3 0) l) = l)))) := by
  -- 32 universal binders (4 states × 8 var groups each).
  -- s0 / s1: 16 vars, names not needed.
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  -- s2: n_s2, m_s2, result_s2, i_s2, j_s2, A_s2, B_s2, ed_s2 — name i_s2.
  intro _ _ _ i_s2 _ _ _ _
  -- s3: 8 vars, names not needed (i_s3 etc. eliminated by subst).
  intro _ _ _ _ _ _ _ _
  intro _ _ _ h_n0 h_m0 _ h_col0 h_row0 h_enc_g
  intro h_jeq1 h_neq1 h_meq1 h_req1 h_ieq1 h_Aeq1 h_Beq1 h_edeq1
  intro h_i2_ge1 h_i2_le_n h_j2_ge1 h_j2_le_m1 h_n2 h_m2
  intro h_table h_curr h_col02 h_row02 h_notg
  intro h_n21 h_m21 h_r21 h_i21 h_A21 h_B21
  intro h_ieq3 h_n3 h_m3 h_r3 h_j3 h_A3 h_B3 h_ed3
  -- Substitute every chain frame eq + transition.
  subst h_jeq1 h_neq1 h_meq1 h_req1 h_ieq1 h_Aeq1 h_Beq1 h_edeq1
  subst h_n21 h_m21 h_r21 h_i21 h_A21 h_B21
  subst h_ieq3 h_n3 h_m3 h_r3 h_j3 h_A3 h_B3 h_ed3
  -- Goal now uses s2 names (i_s3 → i_s2 + 1 via h_ieq3).
  refine ⟨?_, ?_, h_n2, h_m2, ?_, h_col02, h_row02⟩
  · omega
  · omega
  -- Table extension to i_s2 + 1.
  intro p q ⟨h_p0, h_p_lt, h_q0, h_qm⟩
  by_cases hp : p = i_s2
  · subst hp
    -- ed_s2 i_s2 q = edit_dist A_s2 i_s2 B_s2 q
    -- ¬g: j_s2 > m_s2.  Bound: j_s2 ≤ m_s2+1.  So j_s2 = m_s2+1.
    -- q ≤ m_s2 < j_s2 → apply h_curr.
    exact h_curr q ⟨h_q0, by omega⟩
  · exact h_table p q ⟨h_p0, by omega, h_q0, h_qm⟩
