/-
K.3.2 3-nested-loop AP search with FLIP — Tier-3 helpers.

Same six helpers as the search-only variant
(SynthLean.Y2Corpus.l16_aug3_three_loops.Helpers), but the
inner break helper now proves MI preservation through the
4-point Update chain that performs the actual AP flip.

τ_L2 carries one EXTRA atom (`0 ≤ w` at index 7) — load-
bearing because the new MI proof writes `w` at position
`M v` and we need w ∈ [0, n).

The MI proof is a 5-way case-split (k = w, k = M v, k = v,
k = u, else) via `split_ifs` on the unfolded store chain.
-/
import SynthLean.Basic
open SynthLean

namespace SynthLean.Y2Corpus.L16Aug3ThreeLoopsFlip

-- sc1: L1 entry-bundle.  Identical to the search-only helper.
theorem k32_3lf_middle_entry :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    (-1 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    (u_s1 = u_s0 + 1) → (v_s1 = -1) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (w_s1 = w_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    (-1 ≤ v_s1) ∧ (v_s1 ≤ n_s1 - 1) ∧
    (0 ≤ u_s1) ∧ (u_s1 ≤ n_s1 - 1) ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n_s1 ∧ M_s1 k ≠ -1) → (0 ≤ M_s1 k ∧ M_s1 k < n_s1)) := by
  intros n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0
         n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1
         h_pre_n h_pre_mi h_pre_sym
         h_u_lo h_u_hi h_found h_mi_outer
         h_g h_trans_u h_trans_v h_frame_n h_frame_found h_frame_w
         h_frame_M h_frame_G
  subst h_trans_u h_trans_v h_frame_n h_frame_found h_frame_w
        h_frame_M h_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact h_mi_outer

-- sc2: L2 entry-bundle.  Identical to search-only (τ_L2 atom 7
-- = `0 ≤ w` is added; the goal of L2 entry includes it).
theorem k32_3lf_inner_entry :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    (-1 ≤ v_s0) → (v_s0 ≤ n_s0 - 1) →
    (0 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    (v_s1 = v_s0 + 1) → (w_s1 = 0) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (u_s1 = u_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- Goal: τ_L2 at s1 (8 conjuncts; atom 7 `0 ≤ w` added)
    (w_s1 ≤ n_s1) ∧ (0 ≤ v_s1) ∧ (v_s1 ≤ n_s1 - 1) ∧
    (0 ≤ u_s1) ∧ (u_s1 ≤ n_s1 - 1) ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n_s1 ∧ M_s1 k ≠ -1) → (0 ≤ M_s1 k ∧ M_s1 k < n_s1)) ∧
    (0 ≤ w_s1) := by
  intros n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0
         n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1
         h_pre_n h_pre_mi h_pre_sym
         h_v_lo h_v_hi h_u_lo h_u_hi h_found h_mi_outer
         h_g h_trans_v h_trans_w h_frame_n h_frame_found h_frame_u
         h_frame_M h_frame_G
  subst h_trans_v h_trans_w h_frame_n h_frame_found h_frame_u
        h_frame_M h_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · exact h_u_lo
  · exact h_u_hi
  · omega
  · exact h_mi_outer
  · omega

-- sc4: L2 inner break with AP FLIP.  This is the new helper —
-- proves MI(new_M, n) via 5-way case-split on k.
theorem k32_3lf_inner_break :
    ∀ (n found u v w : Int)
      (M : Int → Int) (G : Int → Int → Int)
      (found' : Int) (M' : Int → Int),
    (n ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) → G p q = G q p) →
    -- τ_L2 (full, 8 atoms)
    (w ≤ n) → (0 ≤ v) → (v ≤ n - 1) →
    (0 ≤ u) → (u ≤ n - 1) →
    (found = 0 ∨ found = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (0 ≤ w) →
    -- Combined guard
    (w < n ∧ v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧
     w ≠ u ∧ w ≠ v ∧ w ≠ M v ∧ M w = -1 ∧
     G (M v) w ≥ 1 ∧ M u = -1) →
    -- Trans: M' is the 4-point flip
    (M' = store (store (store (store M u v) v u) (M v) w) w (M v)) →
    (found' = 1) →
    -- Goal: τ_L1 at body_out
    (-1 ≤ v) ∧ (v ≤ n - 1) ∧ (0 ≤ u) ∧ (u ≤ n - 1) ∧
    (found' = 0 ∨ found' = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M' k ≠ -1) → (0 ≤ M' k ∧ M' k < n)) := by
  intros n found u v w M G found' M'
         h_pre_n h_pre_mi h_pre_sym
         h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 h_tau_7
         h_guard h_trans_M h_trans_found
  obtain ⟨h_g_w, h_g_uv, h_g_Gpos, h_g_Mv, h_g_wu, h_g_wv, h_g_wMv,
          h_g_Mw, h_g_Gz, h_g_Mu⟩ := h_guard
  have h_Mv_in : 0 ≤ M v ∧ M v < n :=
    h_pre_mi v ⟨h_tau_1, by omega, h_g_Mv⟩
  refine ⟨by omega, h_tau_2, h_tau_3, h_tau_4, by omega, ?_⟩
  intros k h_k
  obtain ⟨h_k_lo, h_k_hi, h_k_ne⟩ := h_k
  rw [h_trans_M] at h_k_ne ⊢
  simp only [store] at h_k_ne ⊢
  split_ifs at h_k_ne ⊢ with h1 h2 h3 h4
  · exact h_Mv_in
  · exact ⟨h_tau_7, by omega⟩
  · exact ⟨h_tau_3, by omega⟩
  · exact ⟨h_tau_1, by omega⟩
  · exact h_pre_mi k ⟨h_k_lo, h_k_hi, h_k_ne⟩

-- sc8: L1 chain-bundle-post (middle body inductive).  Same shape
-- as search-only, but τ_L2 now has 8 atoms (atom 7 = `0 ≤ w`).
theorem k32_3lf_middle_body_ind :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 found_s2 u_s2 v_s2 w_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    (-1 ≤ v_s0) → (v_s0 ≤ n_s0 - 1) →
    (0 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    (v_s1 = v_s0 + 1) → (w_s1 = 0) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (u_s1 = u_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- L2 abstract: 8 τ_L2 atoms + frame (NO ¬g)
    (w_s2 ≤ n_s2) → (0 ≤ v_s2) → (v_s2 ≤ n_s2 - 1) →
    (0 ≤ u_s2) → (u_s2 ≤ n_s2 - 1) →
    (found_s2 = 0 ∨ found_s2 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) →
    (0 ≤ w_s2) →
    (n_s2 = n_s1) → (u_s2 = u_s1) → (v_s2 = v_s1) →
    (G_s2 = G_s1) →
    (-1 ≤ v_s2) ∧ (v_s2 ≤ n_s2 - 1) ∧
    (0 ≤ u_s2) ∧ (u_s2 ≤ n_s2 - 1) ∧
    (found_s2 = 0 ∨ found_s2 = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) := by
  intros n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0
         n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1
         n_s2 found_s2 u_s2 v_s2 w_s2 M_s2 G_s2
         h_pre_n h_pre_mi h_pre_sym
         h_v_lo h_v_hi h_u_lo h_u_hi h_found h_mi
         h_g
         h_trans_v h_trans_w h_frame_n h_frame_found h_frame_u
         h_frame_M h_frame_G
         h_l2_w h_l2_v_lo h_l2_v_hi h_l2_u_lo h_l2_u_hi
         h_l2_found h_l2_mi h_l2_w_lo
         h_l2_frame_n h_l2_frame_u h_l2_frame_v h_l2_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact h_l2_v_hi
  · exact h_l2_u_lo
  · exact h_l2_u_hi
  · exact h_l2_found
  · exact h_l2_mi

-- sc10: L0 chain-bundle-post (outer body inductive).  Identical
-- to search-only (τ_L1 hasn't changed).
theorem k32_3lf_outer_body_ind :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 found_s2 u_s2 v_s2 w_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    (-1 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    (u_s1 = u_s0 + 1) → (v_s1 = -1) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (w_s1 = w_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    (-1 ≤ v_s2) → (v_s2 ≤ n_s2 - 1) →
    (0 ≤ u_s2) → (u_s2 ≤ n_s2 - 1) →
    (found_s2 = 0 ∨ found_s2 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) →
    (¬ (v_s2 + 1 < n_s2 ∧ found_s2 = 0)) →
    (n_s2 = n_s1) → (u_s2 = u_s1) →
    (G_s2 = G_s1) →
    (-1 ≤ u_s2) ∧ (u_s2 ≤ n_s2 - 1) ∧
    (found_s2 = 0 ∨ found_s2 = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) := by
  intros n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0
         n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1
         n_s2 found_s2 u_s2 v_s2 w_s2 M_s2 G_s2
         h_pre_n h_pre_mi h_pre_sym
         h_u_lo h_u_hi h_found h_mi
         h_g
         h_trans_u h_trans_v h_frame_n h_frame_found h_frame_w
         h_frame_M h_frame_G
         h_l1_v_lo h_l1_v_hi h_l1_u_lo h_l1_u_hi h_l1_found h_l1_mi
         h_l1_not_g
         h_l1_frame_n h_l1_frame_u h_l1_frame_G
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact h_l1_found
  · exact h_l1_mi

-- sc12: L0 final bundle (FLAT shape; M is now primed since
-- L0's body modifies it via the AP flip).
theorem k32_3lf_final :
    ∀ (n u v w found : Int)
      (M : Int → Int) (G : Int → Int → Int)
      (u' v' w' found' : Int) (M' : Int → Int),
    (n ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) → G p q = G q p) →
    (-1 ≤ u') → (u' ≤ n - 1) →
    (found' = 0 ∨ found' = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M' k ≠ -1) → (0 ≤ M' k ∧ M' k < n)) →
    (¬ (u' + 1 < n ∧ found' = 0)) →
    -- Goal: Fpost = MI(M', n) ∧ found' ∈ {0, 1}.
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M' k ≠ -1) → (0 ≤ M' k ∧ M' k < n)) ∧
    (found' = 0 ∨ found' = 1) := by
  intros n u v w found M G u' v' w' found' M'
         h_pre_n h_pre_mi h_pre_sym
         h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_not_g
  exact ⟨h_tau_3, h_tau_2⟩

end SynthLean.Y2Corpus.L16Aug3ThreeLoopsFlip
