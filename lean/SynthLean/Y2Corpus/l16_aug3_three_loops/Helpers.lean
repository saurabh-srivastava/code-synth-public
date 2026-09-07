/-
K.3.2 3-nested-loop AP search — Tier-3 helpers.

Five helpers cover the heavy obligations:
  - k32_3l_inner_entry      (sc2,  L2 entry-bundle)
  - k32_3l_inner_break      (sc4,  L2 break, br=0; consequent τ_L1)
  - k32_3l_middle_body_ind  (sc8,  L1 chain-bundle-post via L2)
  - k32_3l_outer_body_ind   (sc10, L0 chain-bundle-post via L1)
  - k32_3l_final            (sc12, L0 final bundle ⇒ post)

The algorithm doesn't modify M; MI is carried trivially through
frame equations.  Every helper closes via omega + direct
hypothesis citations.
-/
import SynthLean.Basic
open SynthLean

namespace SynthLean.Y2Corpus.L16Aug3ThreeLoops

-- sc1: L1 entry-bundle.  After B1 (u := u+1, v := -1) inside
-- L0's body, prove τ_L1 at s1.
theorem k32_3l_middle_entry :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    -- Pre
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    -- τ_L0 at s0
    (-1 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    -- g_L0
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- B1 trans + frame (s0 → s1)
    (u_s1 = u_s0 + 1) → (v_s1 = -1) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (w_s1 = w_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- Goal: τ_L1 at s1
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

-- sc2: L2 entry-bundle.  After B2 (v := v+1, w := 0) inside
-- L1's body, prove τ_L2 at s1.
theorem k32_3l_inner_entry :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    -- Pre
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    -- τ_L1 at s0
    (-1 ≤ v_s0) → (v_s0 ≤ n_s0 - 1) →
    (0 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    -- g_L1
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- B2 trans + frame
    (v_s1 = v_s0 + 1) → (w_s1 = 0) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (u_s1 = u_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- Goal: τ_L2 at s1
    (w_s1 ≤ n_s1) ∧ (0 ≤ v_s1) ∧ (v_s1 ≤ n_s1 - 1) ∧
    (0 ≤ u_s1) ∧ (u_s1 ≤ n_s1 - 1) ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n_s1 ∧ M_s1 k ≠ -1) → (0 ≤ M_s1 k ∧ M_s1 k < n_s1)) := by
  intros n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0
         n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1
         h_pre_n h_pre_mi h_pre_sym
         h_v_lo h_v_hi h_u_lo h_u_hi h_found h_mi_outer
         h_g h_trans_v h_trans_w h_frame_n h_frame_found h_frame_u
         h_frame_M h_frame_G
  subst h_trans_v h_trans_w h_frame_n h_frame_found h_frame_u
        h_frame_M h_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · exact h_u_lo
  · exact h_u_hi
  · omega
  · exact h_mi_outer

-- sc4: L2 inner break (branch_idx=0).  Only `found` changes.
-- Consequent: τ_L1 (the immediately enclosing Loop).
theorem k32_3l_inner_break :
    ∀ (n found u v w : Int)
      (M : Int → Int) (G : Int → Int → Int)
      (found' : Int),
    -- Pre
    (n ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) → G p q = G q p) →
    -- τ_L2 (full)
    (w ≤ n) → (0 ≤ v) → (v ≤ n - 1) →
    (0 ≤ u) → (u ≤ n - 1) →
    (found = 0 ∨ found = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    -- Combined guard
    (w < n ∧ v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧
     w ≠ u ∧ w ≠ v ∧ w ≠ M v ∧ M w = -1 ∧
     G (M v) w ≥ 1 ∧ M u = -1) →
    (found' = 1) →
    -- Goal: τ_L1 at body_out
    (-1 ≤ v) ∧ (v ≤ n - 1) ∧ (0 ≤ u) ∧ (u ≤ n - 1) ∧
    (found' = 0 ∨ found' = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) := by
  intros n found u v w M G found'
         h_pre_n h_pre_mi h_pre_sym
         h_tau_w h_tau_v_lo h_tau_v_hi h_tau_u_lo h_tau_u_hi
         h_tau_found h_tau_mi h_guard h_trans_found
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact h_tau_v_hi
  · exact h_tau_u_lo
  · exact h_tau_u_hi
  · omega
  · exact h_tau_mi

-- sc8: L1 chain-bundle-post.  Middle loop's body inductive
-- through Loop(L2).  L2 is break-capable, so NO ¬g_L2.
theorem k32_3l_middle_body_ind :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 found_s2 u_s2 v_s2 w_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    -- Pre
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    -- τ_L1 at s0
    (-1 ≤ v_s0) → (v_s0 ≤ n_s0 - 1) →
    (0 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    -- g_L1
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- B2 trans + frame
    (v_s1 = v_s0 + 1) → (w_s1 = 0) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (u_s1 = u_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- L2 abstract: τ_L2 at s2 + frame (NO ¬g_L2)
    (w_s2 ≤ n_s2) → (0 ≤ v_s2) → (v_s2 ≤ n_s2 - 1) →
    (0 ≤ u_s2) → (u_s2 ≤ n_s2 - 1) →
    (found_s2 = 0 ∨ found_s2 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) →
    (n_s2 = n_s1) → (u_s2 = u_s1) → (v_s2 = v_s1) →
    (M_s2 = M_s1) → (G_s2 = G_s1) →
    -- Goal: τ_L1 at s2
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
         h_l2_found h_l2_mi
         h_l2_frame_n h_l2_frame_u h_l2_frame_v h_l2_frame_M h_l2_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact h_l2_v_hi
  · exact h_l2_u_lo
  · exact h_l2_u_hi
  · exact h_l2_found
  · exact h_l2_mi

-- sc10: L0 chain-bundle-post.  Outer loop's body inductive
-- through Loop(L1).  L1 is NOT break-capable, so we DO have ¬g_L1.
theorem k32_3l_outer_body_ind :
    ∀ (n_s0 found_s0 u_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 found_s1 u_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 found_s2 u_s2 v_s2 w_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    -- Pre
    (n_s0 ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    -- τ_L0 at s0
    (-1 ≤ u_s0) → (u_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    -- g_L0
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- B1 trans + frame
    (u_s1 = u_s0 + 1) → (v_s1 = -1) →
    (n_s1 = n_s0) → (found_s1 = found_s0) → (w_s1 = w_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- L1 abstract: τ_L1 at s2 + ¬g_L1 + frame
    (-1 ≤ v_s2) → (v_s2 ≤ n_s2 - 1) →
    (0 ≤ u_s2) → (u_s2 ≤ n_s2 - 1) →
    (found_s2 = 0 ∨ found_s2 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) →
    (¬ (v_s2 + 1 < n_s2 ∧ found_s2 = 0)) →
    (n_s2 = n_s1) → (u_s2 = u_s1) →
    (M_s2 = M_s1) → (G_s2 = G_s1) →
    -- Goal: τ_L0 at s2
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
         h_l1_frame_n h_l1_frame_u h_l1_frame_M h_l1_frame_G
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact h_l1_found
  · exact h_l1_mi

-- sc12: L0 final bundle.  Flat-shape signature (the dispatch
-- uses theorem_for_chain_bundle, not the chain-aware variant,
-- because L0's chain prefix has no non-SB items and L0 is at
-- the top level).  Pre-loop vars: (n, u, v, w, found, M, G).
-- Post-loop primed: (u', v', w', found').  M and n are not
-- modified by the loop so they aren't primed.
theorem k32_3l_final :
    ∀ (n u v w found : Int)
      (M : Int → Int) (G : Int → Int → Int)
      (u' v' w' found' : Int),
    -- Pre
    (n ≥ 0) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (∀ p q : Int, (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) → G p q = G q p) →
    -- τ_L0 at post (4 atoms)
    (-1 ≤ u') → (u' ≤ n - 1) →
    (found' = 0 ∨ found' = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    -- ¬g_L0 at post
    (¬ (u' + 1 < n ∧ found' = 0)) →
    -- Goal: Fpost = MI(M, n) ∧ found' ∈ {0, 1}.
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) ∧
    (found' = 0 ∨ found' = 1) := by
  intros n u v w found M G u' v' w' found'
         h_pre_n h_pre_mi h_pre_sym
         h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_not_g
  exact ⟨h_pre_mi, h_tau_2⟩

end SynthLean.Y2Corpus.L16Aug3ThreeLoops
