/-
K.3.2 2-loop AP search — Tier-3 helpers.

The 2-nested-loop augmenting-path SEARCH (no flip): outer
iterates v in [-1, n-1], inner iterates w in [0, n].  Inner
break sets `found := 1`; outer guard `found == 0` short-
circuits remaining outer iterations.

Three helpers cover the entry-bundle (sc1), the inner-body
break-bundle (the inner break exits to enclosing L0), and
the outer-body bundle (sc7 — chain through inner Loop).

All proofs are pure omega / direct hypothesis citations
since the algorithm doesn't modify M (only the `found` flag
and counters change).  MI is carried through unchanged.
-/
import SynthLean.Basic
open SynthLean

namespace SynthLean.Y2Corpus.L16Aug3TwoLoops

-- sc1: L1 entry-bundle.  After B0 (init) and B1 (increment v,
-- reset w), prove τ_L1 at the state entering inner loop.
theorem k32_2l_inner_entry :
    ∀ (n_s0 u_s0 found_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int)
      (G_s0 : Int → Int → Int)
      (n_s1 u_s1 found_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int)
      (G_s1 : Int → Int → Int),
    -- Pre
    (n_s0 ≥ 0) → (0 ≤ u_s0) → (u_s0 < n_s0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (M_s0 u_s0 = -1) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    -- τ_L0
    (-1 ≤ v_s0) →
    (v_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    -- g_L0
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- B1 trans + frame
    (v_s1 = v_s0 + 1) → (w_s1 = 0) →
    (n_s1 = n_s0) → (u_s1 = u_s0) → (found_s1 = found_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- Goal: τ_L1 at s1
    (w_s1 ≤ n_s1) ∧ (0 ≤ v_s1) ∧ (v_s1 ≤ n_s1 - 1) ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n_s1 ∧ M_s1 k ≠ -1) → (0 ≤ M_s1 k ∧ M_s1 k < n_s1)) := by
  intros n_s0 u_s0 found_s0 v_s0 w_s0 M_s0 G_s0
         n_s1 u_s1 found_s1 v_s1 w_s1 M_s1 G_s1
         h_pre_n h_pre_u_lo h_pre_u_hi h_pre_mi h_pre_mu h_pre_sym
         h_tau_neg1_v h_tau_v_n h_tau_found h_tau_mi
         h_g h_trans_v h_trans_w h_frame_n h_frame_u h_frame_found
         h_frame_M h_frame_G
  subst h_trans_v h_trans_w h_frame_n h_frame_u h_frame_found h_frame_M h_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- w_s1 ≤ n_s1: w_s1 = 0, n_s1 = n_s0 ≥ 0
    omega
  · -- 0 ≤ v_s1: v_s1 = v_s0 + 1, v_s0 ≥ -1
    omega
  · -- v_s1 ≤ n_s1 - 1: v_s0 + 1 < n_s0 from g, so v_s0 + 1 ≤ n_s0 - 1
    omega
  · -- found_s1 ∈ {0,1}: found_s1 = found_s0 = 0 (from g)
    omega
  · -- MI(M_s1): M_s1 = M_s0; carried from h_tau_mi
    exact h_tau_mi

-- sc3: inner break-bundle (branch_idx=0).  After the inner branch
-- 0 fires (found := 1, break), prove τ_L0 at the inner body's
-- exit state.  Note: only `found` is modified by the break trans;
-- v, M are preserved via frame eq (handled implicitly since they
-- aren't listed in the transition).
theorem k32_2l_inner_break :
    ∀ (n u found v w : Int)
      (M : Int → Int)
      (G : Int → Int → Int)
      (found' : Int),
    -- Pre
    (n ≥ 0) → (0 ≤ u) → (u < n) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    (M u = -1) →
    (∀ p q : Int, (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) → G p q = G q p) →
    -- τ_L1 (full)
    (w ≤ n) →
    (0 ≤ v) →
    (v ≤ n - 1) →
    (found = 0 ∨ found = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) →
    -- Combined guard (g_L1 ∧ g_branch_0)
    (w < n ∧ v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧ w ≠ u ∧ w ≠ v ∧
     w ≠ M v ∧ M w = -1 ∧ G (M v) w ≥ 1) →
    -- Trans (only `found` modified)
    (found' = 1) →
    -- Goal: τ_L0 at body_out (v, M unchanged; found becomes 1)
    (-1 ≤ v) ∧ (v ≤ n - 1) ∧ (found' = 0 ∨ found' = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n ∧ M k ≠ -1) → (0 ≤ M k ∧ M k < n)) := by
  intros n u found v w M G found'
         h_pre_n h_pre_u_lo h_pre_u_hi h_pre_mi h_pre_mu h_pre_sym
         h_tau_w h_tau_v_lo h_tau_v_hi h_tau_found h_tau_mi
         h_guard h_trans_found
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega    -- -1 ≤ v from 0 ≤ v
  · exact h_tau_v_hi
  · omega    -- found' = 1
  · exact h_tau_mi

-- sc7: outer L0 body inductive (chain-bundle-post via inner Loop).
-- Chain: B1 (v++, w:=0) >> Loop(L1).  L1 is the last item; its
-- exit state is the outer body's terminating state.  Prove
-- τ_L0 at s2 from τ_L0 at s0 + chain hypotheses.
theorem k32_2l_outer_body_inductive :
    ∀ (n_s0 u_s0 found_s0 v_s0 w_s0 : Int)
      (M_s0 : Int → Int)
      (G_s0 : Int → Int → Int)
      (n_s1 u_s1 found_s1 v_s1 w_s1 : Int)
      (M_s1 : Int → Int)
      (G_s1 : Int → Int → Int)
      (n_s2 u_s2 found_s2 v_s2 w_s2 : Int)
      (M_s2 : Int → Int)
      (G_s2 : Int → Int → Int),
    -- Pre
    (n_s0 ≥ 0) → (0 ≤ u_s0) → (u_s0 < n_s0) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    (M_s0 u_s0 = -1) →
    (∀ p q : Int, (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) → G_s0 p q = G_s0 q p) →
    -- τ_L0 at s0
    (-1 ≤ v_s0) →
    (v_s0 ≤ n_s0 - 1) →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s0 ∧ M_s0 k ≠ -1) → (0 ≤ M_s0 k ∧ M_s0 k < n_s0)) →
    -- g_L0
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- B1 trans + frame (s0 → s1)
    (v_s1 = v_s0 + 1) → (w_s1 = 0) →
    (n_s1 = n_s0) → (u_s1 = u_s0) → (found_s1 = found_s0) →
    (M_s1 = M_s0) → (G_s1 = G_s0) →
    -- L1 abstract: τ_L1 at s2 (5 atoms, NO ¬g since break-capable)
    --   + frame eqs for vars not modified by inner (n, u, v, M, G)
    (w_s2 ≤ n_s2) →
    (0 ≤ v_s2) →
    (v_s2 ≤ n_s2 - 1) →
    (found_s2 = 0 ∨ found_s2 = 1) →
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) →
    (n_s2 = n_s1) → (u_s2 = u_s1) → (v_s2 = v_s1) →
    (M_s2 = M_s1) → (G_s2 = G_s1) →
    -- Goal: τ_L0 at s2
    (-1 ≤ v_s2) ∧ (v_s2 ≤ n_s2 - 1) ∧ (found_s2 = 0 ∨ found_s2 = 1) ∧
    (∀ k : Int, (0 ≤ k ∧ k < n_s2 ∧ M_s2 k ≠ -1) → (0 ≤ M_s2 k ∧ M_s2 k < n_s2)) := by
  intros n_s0 u_s0 found_s0 v_s0 w_s0 M_s0 G_s0
         n_s1 u_s1 found_s1 v_s1 w_s1 M_s1 G_s1
         n_s2 u_s2 found_s2 v_s2 w_s2 M_s2 G_s2
         h_pre_n h_pre_u_lo h_pre_u_hi h_pre_mi h_pre_mu h_pre_sym
         h_tau_neg1_v h_tau_v_n h_tau_found h_tau_mi
         h_g h_trans_v h_trans_w h_frame_n h_frame_u h_frame_found h_frame_M h_frame_G
         h_l1_w h_l1_v_lo h_l1_v_hi h_l1_found h_l1_mi
         h_l1_frame_n h_l1_frame_u h_l1_frame_v h_l1_frame_M h_l1_frame_G
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact h_l1_found
  · exact h_l1_mi

end SynthLean.Y2Corpus.L16Aug3TwoLoops
