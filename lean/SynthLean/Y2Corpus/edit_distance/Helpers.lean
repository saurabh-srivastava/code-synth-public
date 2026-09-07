/-
edit_distance Tier-2 helpers — task #158.

Levenshtein-style 2D DP with simplified diagonal-only recurrence
(no insert/delete; only match/mismatch).  Five helpers cover
the obligations the generic tactic chain can't close:

  sc0  L0 entry         (flat)
  sc1  L1 entry         (chain-aware, enclosed by L0)
  sc3  L1 safety br 0   (match case: A[i-1] = B[j-1])
  sc5  L1 safety br 1   (mismatch case: A[i-1] ≠ B[j-1])
  sc8  L1 body inductive (chain-aware nested: L0's body
                          around L1)

sc10 (L0 final post) closes via the generic chain (~5s) — no
helper needed.

Banked as Tier-2 axioms; Tier-1 conversion follows once the
edit_dist recurrence and DP-table propagation lemmas land.
-/
import SynthLean.Basic
open SynthLean

axiom edit_dist : (Int → Int) → Int → (Int → Int) → Int → Int

-- Per-array base / recurrence axioms — mirror Problem.axioms.
axiom ed_user_axiom_0 : ∀ (A B : Int → Int), ((edit_dist A 0 B 0) = 0)
axiom ed_user_axiom_1 : ∀ (A B : Int → Int), (∀ k : Int,
    ((k ≥ 0) → ((edit_dist A (k + 1) B 0) = (k + 1))))
axiom ed_user_axiom_2 : ∀ (A B : Int → Int), (∀ l : Int,
    ((l ≥ 0) → ((edit_dist A 0 B (l + 1)) = (l + 1))))
-- match case
axiom ed_user_axiom_3 : ∀ (A B : Int → Int), (∀ k l : Int,
    (((k ≥ 0) ∧ (l ≥ 0) ∧ ((A k) = (B l))) →
     ((edit_dist A (k + 1) B (l + 1)) = (edit_dist A k B l))))
-- mismatch case (diagonal-only)
axiom ed_user_axiom_4 : ∀ (A B : Int → Int), (∀ k l : Int,
    (((k ≥ 0) ∧ (l ≥ 0) ∧ ¬ ((A k) = (B l))) →
     ((edit_dist A (k + 1) B (l + 1)) = (1 + (edit_dist A k B l)))))

namespace SynthLean.EditDistanceHelpers

-- sc0: L0 entry (i := 1 from init).  Goal: τ@L0 at s1.
-- Tier-1 theorem: with i' = 1, all conjuncts follow by direct
-- appeal to h_pre or via ed_user_axiom_{0,2} for the row-0
-- correspondence (case-split on q = 0).
theorem ed_l0_entry :
    ∀ (n m result i j : Int)
      (A B : Int → Int)
      (ed : Int → Int → Int)
      (i' : Int),
    ((n ≥ 0) ∧ (m ≥ 0)
       ∧ (∀ k : Int, (((0 ≤ k) ∧ (k ≤ n)) → (((ed k) 0) = k)))
       ∧ (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed 0) l) = l)))) →
    (i' = 1) →
    ((1 ≤ i') ∧ (i' ≤ (n + 1)) ∧ (n ≥ 0) ∧ (m ≥ 0) ∧
     (∀ p q : Int, (((0 ≤ p) ∧ (p < i') ∧ (0 ≤ q) ∧ (q ≤ m)) → (((ed p) q) = (edit_dist A p B q)))) ∧
     (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n)) → (((ed p) 0) = p))) ∧
     (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed 0) l) = l)))) := by
  intro n m result i j A B ed i' h_pre h_init
  subst h_init
  obtain ⟨h_n, h_m, h_col0, h_row0⟩ := h_pre
  refine ⟨?_, ?_, h_n, h_m, ?_, h_col0, h_row0⟩
  · omega
  · omega
  -- ∀ p q. 0 ≤ p < 1 ∧ 0 ≤ q ≤ m → ed[p][q] = edit_dist(A, p, B, q)
  intro p q ⟨_, h_p1, h_q0, h_qm⟩
  have hp0 : p = 0 := by omega
  subst hp0
  rw [h_row0 q ⟨h_q0, h_qm⟩]
  by_cases hq : q = 0
  · subst hq; exact (ed_user_axiom_0 A B).symm
  · have hq_ge1 : q ≥ 1 := by omega
    have h_ax := ed_user_axiom_2 A B (q - 1) (by omega)
    have h_arg : (q - 1) + 1 = q := by omega
    rw [h_arg] at h_ax
    exact h_ax.symm

-- sc1: L1 entry (after SB1 sets j := 1).  Goal: τ@L1 at s1.
-- Tier-1 theorem: all conjuncts follow from h_enc_tau_* and the
-- transition/frame eqs.  Conjunct 8 (current row at j_s1=1
-- means q=0) needs ed_user_axiom_1 to relate ed[i][0]=i and
-- edit_dist(A, i, B, 0)=i.
theorem ed_l1_entry_chain :
    ∀ (n_s0 m_s0 result_s0 i_s0 j_s0 : Int)
      (A_s0 B_s0 : Int → Int)
      (ed_s0 : Int → Int → Int)
      (n_s1 m_s1 result_s1 i_s1 j_s1 : Int)
      (A_s1 B_s1 : Int → Int)
      (ed_s1 : Int → Int → Int),
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
    ((1 ≤ i_s1) ∧ (i_s1 ≤ n_s1) ∧ (1 ≤ j_s1) ∧ (j_s1 ≤ (m_s1 + 1)) ∧ (n_s1 ≥ 0) ∧ (m_s1 ≥ 0) ∧
     (∀ p q : Int, (((0 ≤ p) ∧ (p < i_s1) ∧ (0 ≤ q) ∧ (q ≤ m_s1)) → (((ed_s1 p) q) = (edit_dist A_s1 p B_s1 q)))) ∧
     (∀ q : Int, (((0 ≤ q) ∧ (q < j_s1)) → (((ed_s1 i_s1) q) = (edit_dist A_s1 i_s1 B_s1 q)))) ∧
     (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n_s1)) → (((ed_s1 p) 0) = p))) ∧
     (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m_s1)) → (((ed_s1 0) l) = l)))) := by
  intro _ _ _ _ _ _ _ _
  intro _ _ _ i_s1 _ A_s1 B_s1 _
  intro _ h_i_ge1 _ h_n h_m h_table h_col0 h_row0 h_enc_g
  intro h_jeq h_neq h_meq _ h_ieq h_Aeq h_Beq h_edeq
  subst h_jeq h_neq h_meq h_ieq h_Aeq h_Beq h_edeq
  refine ⟨h_i_ge1, h_enc_g, ?_, ?_, h_n, h_m, h_table, ?_, h_col0, h_row0⟩
  · omega
  · omega
  -- Current row at j=1: only q=0 in range.
  intro q ⟨h_q0, h_q1⟩
  have hq : q = 0 := by omega
  subst hq
  rw [h_col0 _ ⟨by omega, h_enc_g⟩]
  -- Goal: i_s1 = edit_dist A_s1 i_s1 B_s1 0
  have h_ax := ed_user_axiom_1 A_s1 B_s1 (i_s1 - 1) (by omega)
  have h_arg : (i_s1 - 1) + 1 = i_s1 := by omega
  rw [h_arg] at h_ax
  exact h_ax.symm

-- sc3: L1 inductive branch 0 (match case).
-- ed' = store2d ed i j ed[i-1][j-1]; j' = j+1.
-- Tier-1: row-i extension uses ed_user_axiom_3 (match case).
theorem ed_l1_inductive_branch_0 :
    ∀ (n m result i j : Int)
      (A B : Int → Int)
      (ed : Int → Int → Int)
      (j' : Int) (ed' : Int → Int → Int),
    ((n ≥ 0) ∧ (m ≥ 0)
       ∧ (∀ k : Int, (((0 ≤ k) ∧ (k ≤ n)) → (((ed k) 0) = k)))
       ∧ (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed 0) l) = l)))) →
    (1 ≤ i) → (i ≤ n) → (1 ≤ j) → (j ≤ (m + 1)) → (n ≥ 0) → (m ≥ 0) →
    (∀ p q : Int, (((0 ≤ p) ∧ (p < i) ∧ (0 ≤ q) ∧ (q ≤ m)) → (((ed p) q) = (edit_dist A p B q)))) →
    (∀ q : Int, (((0 ≤ q) ∧ (q < j)) → (((ed i) q) = (edit_dist A i B q)))) →
    (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n)) → (((ed p) 0) = p))) →
    (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed 0) l) = l))) →
    ((j ≤ m) ∧ ((A (i - 1)) = (B (j - 1)))) →
    (ed' = (store2d ed i j ((ed (i - 1)) (j - 1)))) →
    (j' = (j + 1)) →
    ((1 ≤ i) ∧ (i ≤ n) ∧ (1 ≤ j') ∧ (j' ≤ (m + 1)) ∧ (n ≥ 0) ∧ (m ≥ 0) ∧
     (∀ p q : Int, (((0 ≤ p) ∧ (p < i) ∧ (0 ≤ q) ∧ (q ≤ m)) → (((ed' p) q) = (edit_dist A p B q)))) ∧
     (∀ q : Int, (((0 ≤ q) ∧ (q < j')) → (((ed' i) q) = (edit_dist A i B q)))) ∧
     (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n)) → (((ed' p) 0) = p))) ∧
     (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed' 0) l) = l)))) := by
  intro n m _ i j A B ed j' ed'
  intro _ h_i_ge1 h_i_le_n _ _ h_n h_m
  intro h_table h_curr h_col0 h_row0 h_guard h_edeq h_jeq
  subst h_edeq h_jeq
  obtain ⟨h_j_le_m, h_match⟩ := h_guard
  refine ⟨h_i_ge1, h_i_le_n, ?_, ?_, h_n, h_m, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  -- Prior rows unchanged: p < i but store writes at row i.
  · intro p q ⟨h_p0, h_p_lt, h_q0, h_qm⟩
    show (store2d ed i j ((ed (i - 1)) (j - 1))) p q = edit_dist A p B q
    unfold store2d
    have h_ne : ¬ (p = i ∧ q = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_table p q ⟨h_p0, h_p_lt, h_q0, h_qm⟩
  -- Current row extended.
  · intro q ⟨h_q0, h_q_lt⟩
    show (store2d ed i j ((ed (i - 1)) (j - 1))) i q = edit_dist A i B q
    unfold store2d
    by_cases hq : q = j
    · have h_eq : (i = i ∧ q = j) := ⟨rfl, hq⟩
      rw [if_pos h_eq]
      have h_ax := ed_user_axiom_3 A B (i - 1) (j - 1)
        ⟨by omega, by omega, by simpa using h_match⟩
      have h_argi : (i - 1) + 1 = i := by omega
      have h_argj : (j - 1) + 1 = j := by omega
      rw [h_argi, h_argj] at h_ax
      have h_tab := h_table (i - 1) (j - 1)
        ⟨by omega, by omega, by omega, by omega⟩
      rw [hq, h_tab]; exact h_ax.symm
    · have h_ne : ¬ (i = i ∧ q = j) := fun h => hq h.2
      rw [if_neg h_ne]
      exact h_curr q ⟨h_q0, by omega⟩
  -- Column 0 unchanged: store at column j ≥ 1.
  · intro p ⟨h_p0, h_pn⟩
    show (store2d ed i j ((ed (i - 1)) (j - 1))) p 0 = p
    unfold store2d
    have h_ne : ¬ (p = i ∧ (0 : Int) = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_col0 p ⟨h_p0, h_pn⟩
  -- Row 0 unchanged: store at row i ≥ 1.
  · intro l ⟨h_l0, h_lm⟩
    show (store2d ed i j ((ed (i - 1)) (j - 1))) 0 l = l
    unfold store2d
    have h_ne : ¬ ((0 : Int) = i ∧ l = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_row0 l ⟨h_l0, h_lm⟩

-- sc5: L1 inductive branch 1 (mismatch case).
-- ed' = store2d ed i j (1 + ed[i-1][j-1]); j' = j+1.
-- Tier-1: same shape as branch_0; uses ed_user_axiom_4.
theorem ed_l1_inductive_branch_1 :
    ∀ (n m result i j : Int)
      (A B : Int → Int)
      (ed : Int → Int → Int)
      (j' : Int) (ed' : Int → Int → Int),
    ((n ≥ 0) ∧ (m ≥ 0)
       ∧ (∀ k : Int, (((0 ≤ k) ∧ (k ≤ n)) → (((ed k) 0) = k)))
       ∧ (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed 0) l) = l)))) →
    (1 ≤ i) → (i ≤ n) → (1 ≤ j) → (j ≤ (m + 1)) → (n ≥ 0) → (m ≥ 0) →
    (∀ p q : Int, (((0 ≤ p) ∧ (p < i) ∧ (0 ≤ q) ∧ (q ≤ m)) → (((ed p) q) = (edit_dist A p B q)))) →
    (∀ q : Int, (((0 ≤ q) ∧ (q < j)) → (((ed i) q) = (edit_dist A i B q)))) →
    (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n)) → (((ed p) 0) = p))) →
    (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed 0) l) = l))) →
    ((j ≤ m) ∧ ¬ ((A (i - 1)) = (B (j - 1)))) →
    (ed' = (store2d ed i j (1 + ((ed (i - 1)) (j - 1))))) →
    (j' = (j + 1)) →
    ((1 ≤ i) ∧ (i ≤ n) ∧ (1 ≤ j') ∧ (j' ≤ (m + 1)) ∧ (n ≥ 0) ∧ (m ≥ 0) ∧
     (∀ p q : Int, (((0 ≤ p) ∧ (p < i) ∧ (0 ≤ q) ∧ (q ≤ m)) → (((ed' p) q) = (edit_dist A p B q)))) ∧
     (∀ q : Int, (((0 ≤ q) ∧ (q < j')) → (((ed' i) q) = (edit_dist A i B q)))) ∧
     (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n)) → (((ed' p) 0) = p))) ∧
     (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed' 0) l) = l)))) := by
  intro n m _ i j A B ed j' ed'
  intro _ h_i_ge1 h_i_le_n _ _ h_n h_m
  intro h_table h_curr h_col0 h_row0 h_guard h_edeq h_jeq
  subst h_edeq h_jeq
  obtain ⟨h_j_le_m, h_mismatch⟩ := h_guard
  refine ⟨h_i_ge1, h_i_le_n, ?_, ?_, h_n, h_m, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro p q ⟨h_p0, h_p_lt, h_q0, h_qm⟩
    show (store2d ed i j (1 + (ed (i - 1)) (j - 1))) p q = edit_dist A p B q
    unfold store2d
    have h_ne : ¬ (p = i ∧ q = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_table p q ⟨h_p0, h_p_lt, h_q0, h_qm⟩
  · intro q ⟨h_q0, h_q_lt⟩
    show (store2d ed i j (1 + (ed (i - 1)) (j - 1))) i q = edit_dist A i B q
    unfold store2d
    by_cases hq : q = j
    · have h_eq : (i = i ∧ q = j) := ⟨rfl, hq⟩
      rw [if_pos h_eq]
      have h_ax := ed_user_axiom_4 A B (i - 1) (j - 1)
        ⟨by omega, by omega, by simpa using h_mismatch⟩
      have h_argi : (i - 1) + 1 = i := by omega
      have h_argj : (j - 1) + 1 = j := by omega
      rw [h_argi, h_argj] at h_ax
      have h_tab := h_table (i - 1) (j - 1)
        ⟨by omega, by omega, by omega, by omega⟩
      rw [hq, h_tab]; exact h_ax.symm
    · have h_ne : ¬ (i = i ∧ q = j) := fun h => hq h.2
      rw [if_neg h_ne]
      exact h_curr q ⟨h_q0, by omega⟩
  · intro p ⟨h_p0, h_pn⟩
    show (store2d ed i j (1 + (ed (i - 1)) (j - 1))) p 0 = p
    unfold store2d
    have h_ne : ¬ (p = i ∧ (0 : Int) = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_col0 p ⟨h_p0, h_pn⟩
  · intro l ⟨h_l0, h_lm⟩
    show (store2d ed i j (1 + (ed (i - 1)) (j - 1))) 0 l = l
    unfold store2d
    have h_ne : ¬ ((0 : Int) = i ∧ l = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_row0 l ⟨h_l0, h_lm⟩

-- sc8: L1 body inductive (chain-aware, nested in L0).
-- Chain: SB(B1) j:=1, Loop(L1) abstract, SB(B3) i:=i+1.  4 states.
-- Tier-1: subst all chain frame eqs + transitions; refine 7
-- conjuncts.  Hard conjunct (table extended to row i_s2+1):
-- case-split on p = i_s2.  When p = i_s2, derive j_s2 = m_s2+1
-- from ¬g_L1 + bound, so q ≤ m_s2 < j_s2 lets us apply h_curr.
theorem ed_l1_body_inductive_chain :
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
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro _ _ _ i_s2 _ _ _ _
  intro _ _ _ _ _ _ _ _
  intro _ _ _ h_n0 h_m0 _ h_col0 h_row0 h_enc_g
  intro h_jeq1 h_neq1 h_meq1 h_req1 h_ieq1 h_Aeq1 h_Beq1 h_edeq1
  intro h_i2_ge1 h_i2_le_n h_j2_ge1 h_j2_le_m1 h_n2 h_m2
  intro h_table h_curr h_col02 h_row02 h_notg
  intro h_n21 h_m21 h_r21 h_i21 h_A21 h_B21
  intro h_ieq3 h_n3 h_m3 h_r3 h_j3 h_A3 h_B3 h_ed3
  subst h_jeq1 h_neq1 h_meq1 h_req1 h_ieq1 h_Aeq1 h_Beq1 h_edeq1
  subst h_n21 h_m21 h_r21 h_i21 h_A21 h_B21
  subst h_ieq3 h_n3 h_m3 h_r3 h_j3 h_A3 h_B3 h_ed3
  refine ⟨?_, ?_, h_n2, h_m2, ?_, h_col02, h_row02⟩
  · omega
  · omega
  intro p q ⟨h_p0, h_p_lt, h_q0, h_qm⟩
  by_cases hp : p = i_s2
  · subst hp
    -- ¬g + bound ⇒ j_s2 = m_s2 + 1; q ≤ m_s2 < j_s2.
    exact h_curr q ⟨h_q0, by omega⟩
  · exact h_table p q ⟨h_p0, by omega, h_q0, h_qm⟩

-- sc10: L0 final post.  result' = ed'[n][m] = edit_dist(A, n, B, m).
-- Tier-1: from ¬g (i' > n) + bound (i' ≤ n+1), i' = n+1, so
-- p=n is in [0, i').  τ_outer's table atom at p=n, q=m gives
-- ed'[n][m] = edit_dist(A, n, B, m).  Combine with skip eq.
theorem ed_l0_final_post :
    ∀ (n m result i j : Int)
      (A B : Int → Int)
      (ed : Int → Int → Int)
      (result' i' j' : Int)
      (ed' : Int → Int → Int),
    ((n ≥ 0) ∧ (m ≥ 0)
       ∧ (∀ k : Int, (((0 ≤ k) ∧ (k ≤ n)) → (((ed k) 0) = k)))
       ∧ (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed 0) l) = l)))) →
    (1 ≤ i') → (i' ≤ (n + 1)) → (n ≥ 0) → (m ≥ 0) →
    (∀ p q : Int, (((0 ≤ p) ∧ (p < i') ∧ (0 ≤ q) ∧ (q ≤ m)) → (((ed' p) q) = (edit_dist A p B q)))) →
    (∀ p : Int, (((0 ≤ p) ∧ (p ≤ n)) → (((ed' p) 0) = p))) →
    (∀ l : Int, (((0 ≤ l) ∧ (l ≤ m)) → (((ed' 0) l) = l))) →
    ¬ (i' ≤ n) →
    (result' = ((ed' n) m)) →
    (result' = (edit_dist A n B m)) := by
  intro _ _ _ _ _ A B _ _ i' _ ed'
  intro _ _ h_i_le h_n h_m h_table _ _ h_notg h_skip
  rw [h_skip]
  exact h_table _ _ ⟨h_n, by omega, h_m, le_refl _⟩

end SynthLean.EditDistanceHelpers
