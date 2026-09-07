/-
Scratch: iterating ed_l1_inductive_branch_0 Tier-1 proof.

Per CLAUDE.md rule, iterate complex Lean proofs here before
porting to the canonical Helpers.lean.

Workflow: `lake env lean scratch/ed_inductive_proof_attempt.lean`
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.edit_distance.Helpers
open SynthLean

theorem ed_l1_inductive_branch_0_attempt :
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
  intro h_pre h_i_ge1 h_i_le_n h_j_ge1 h_j_le_m1 h_n h_m
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
      -- Goal: ed (i-1) (j-1) = edit_dist A i B q (q ≡ j via hq).
      -- Use hq.symm to substitute j → q (keep j is not safe;
      -- substituting via `rw [← hq]` keeps both names in scope).
      have h_ax := ed_user_axiom_3 A B (i - 1) (j - 1)
        ⟨by omega, by omega, by simpa using h_match⟩
      have h_argi : (i - 1) + 1 = i := by omega
      have h_argj : (j - 1) + 1 = j := by omega
      rw [h_argi, h_argj] at h_ax
      -- h_ax: edit_dist A i B j = edit_dist A (i-1) B (j-1)
      have h_tab := h_table (i - 1) (j - 1)
        ⟨by omega, by omega, by omega, by omega⟩
      -- h_tab: ed (i-1) (j-1) = edit_dist A (i-1) B (j-1)
      rw [hq, h_tab]; exact h_ax.symm
    · have h_ne : ¬ (i = i ∧ q = j) := fun h => hq h.2
      rw [if_neg h_ne]
      exact h_curr q ⟨h_q0, by omega⟩
  -- Column 0 unchanged: store at column j ≥ 1, never column 0.
  · intro p ⟨h_p0, h_pn⟩
    show (store2d ed i j ((ed (i - 1)) (j - 1))) p 0 = p
    unfold store2d
    have h_ne : ¬ (p = i ∧ (0 : Int) = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_col0 p ⟨h_p0, h_pn⟩
  -- Row 0 unchanged: store at row i ≥ 1, never row 0.
  · intro l ⟨h_l0, h_lm⟩
    show (store2d ed i j ((ed (i - 1)) (j - 1))) 0 l = l
    unfold store2d
    have h_ne : ¬ ((0 : Int) = i ∧ l = j) := fun h => by omega
    rw [if_neg h_ne]
    exact h_row0 l ⟨h_l0, h_lm⟩
