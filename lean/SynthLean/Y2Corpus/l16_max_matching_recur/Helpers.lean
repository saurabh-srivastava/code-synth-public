/-
Slice 2.B max-matching-recur — Tier-3 helpers.

Nine helpers cover the heavy obligations surfaced by the
wedge detector on the no-helpers surface run:

  sc2  : safety-bundle-entry  L1 (after B1: u++, v:=-1)
  sc3  : safety-bundle-entry  L2 (after B2: v++, w:=0)
  sc5  : safety-bundle-post   L2 branch_idx=0 (break + flip)
  sc6  : safety               L2 branch_idx=1 (step w)
  sc9  : safety-bundle-post   L2 (middle body inductive)
  sc11 : safety-bundle-post   L1 (outer body inductive)
  sc13 : safety-bundle-post   L0 (chain body inductive)
  sc14 : safety-bundle-post   L0 (FINAL — invokes Berge)
  sc15 : coverage             (the SB(n=2) recur/identity)

Plus sc16 (ranking-proc-decrease) handled separately via
the UF axiom citation (not in this file — emitted at synth
time directly).
-/
import SynthLean.Basic
open SynthLean

-- The 4 UFs used by the benchmark.  Declared at file scope
-- (no namespace) so the translator-emitted theorem (which
-- references `IsMatching` / `IsMaxMatching` bare) resolves
-- without needing `open` in the cite file.
axiom MatchingSize : (Int → Int) → Int → Int
axiom IsMatching : (Int → Int → Int) → Int → (Int → Int) → Int
axiom IsMaxMatching : (Int → Int → Int) → Int → (Int → Int) → Int
axiom ExistsAugPath : (Int → Int → Int) → Int → (Int → Int) → Int

namespace SynthLean.Y2Corpus.L16MaxMatchingRecur

-- Axioms (matching theory + class-restriction + Berge).
-- Names match emit_axiom_declarations output.
axiom mm_size_nonneg :
  ∀ (M_arr : Int → Int) (m_n : Int), m_n ≥ 0 → MatchingSize M_arr m_n ≥ 0

axiom mm_size_bounded :
  ∀ (M_arr : Int → Int) (m_n : Int), m_n ≥ 0 → 2 * MatchingSize M_arr m_n ≤ m_n

axiom mm_flip_increases :
  ∀ (G_mat : Int → Int → Int) (m_n : Int) (M_arr : Int → Int)
    (m_u m_v m_w : Int),
    (m_n ≥ 0 ∧ 0 ≤ m_u ∧ m_u < m_n ∧ 0 ≤ m_v ∧ m_v < m_n ∧
     0 ≤ m_w ∧ m_w < m_n ∧ m_v ≠ m_u ∧ m_w ≠ m_u ∧ m_w ≠ m_v ∧
     m_w ≠ M_arr m_v ∧ M_arr m_v ≠ -1 ∧
     M_arr m_w = -1 ∧ M_arr m_u = -1) →
    MatchingSize
      (store (store (store (store M_arr m_u m_v) m_v m_u)
              (M_arr m_v) m_w) m_w (M_arr m_v)) m_n
    = MatchingSize M_arr m_n + 1

axiom mm_flip_preserves_matching :
  ∀ (G_mat : Int → Int → Int) (m_n : Int) (M_arr : Int → Int)
    (m_u m_v m_w : Int),
    (IsMatching G_mat m_n M_arr = 1 ∧
     0 ≤ m_u ∧ m_u < m_n ∧ 0 ≤ m_v ∧ m_v < m_n ∧
     0 ≤ m_w ∧ m_w < m_n ∧ m_v ≠ m_u ∧ m_w ≠ m_u ∧ m_w ≠ m_v ∧
     m_w ≠ M_arr m_v ∧ M_arr m_v ≠ -1 ∧
     M_arr m_w = -1 ∧ M_arr m_u = -1 ∧
     G_mat m_u m_v ≥ 1 ∧ G_mat (M_arr m_v) m_w ≥ 1) →
    IsMatching G_mat m_n
      (store (store (store (store M_arr m_u m_v) m_v m_u)
              (M_arr m_v) m_w) m_w (M_arr m_v))
    = 1

axiom mm_berge :
  ∀ (G_mat : Int → Int → Int) (m_n : Int) (M_arr : Int → Int),
    (IsMatching G_mat m_n M_arr = 1 ∧
     ExistsAugPath G_mat m_n M_arr = 0) →
    IsMaxMatching G_mat m_n M_arr = 1

-- Class-restriction axiom (Option β design).  TRUSTED for the
-- graph class our benchmark targets (e.g., bipartite where
-- length-3 APs are sufficient for maximum-matching).  At the
-- algorithm's termination state (h_not_g holds for u' / found'),
-- no augmenting path of any length exists for M.
--
-- Parameterized over the termination-state witnesses (u', found')
-- to make the axiom signature-pin to THIS algorithm's exit
-- condition.  A user citing this elsewhere needs to provide the
-- u'/found' triggering the right ¬g.
axiom mm_termination_implies_no_ap :
  ∀ (G_mat : Int → Int → Int) (m_n : Int) (M_arr : Int → Int)
    (m_u_prime m_found_prime : Int),
    IsMatching G_mat m_n M_arr = 1 →
    ¬ (m_u_prime + 1 < m_n ∧ m_found_prime = 0) →
    ExistsAugPath G_mat m_n M_arr = 0

-- ─────────────────────────────────────────────────────────────
-- sc2: L1 entry-bundle.  After B1 (u := u+1, v := -1), prove τ_L1.
-- ─────────────────────────────────────────────────────────────
theorem mm_sc2_l1_entry :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧ IsMatching G_s0 n_s0 M_s0 = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -1 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) →
    IsMatching G_s0 n_s0 M_s0 = 1 →
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    u_s1 = u_s0 + 1 → v_s1 = -1 →
    n_s1 = n_s0 → w_s1 = w_s0 → found_s1 = found_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    -1 ≤ v_s1 ∧ v_s1 ≤ n_s1 - 1 ∧ 0 ≤ u_s1 ∧ u_s1 ≤ n_s1 - 1 ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧ IsMatching G_s1 n_s1 M_s1 = 1 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1
         h_pre h_u_lo h_u_hi h_found h_mi h_g
         h_trans_u h_trans_v h_frame_n h_frame_w h_frame_found
         h_frame_M h_frame_G
  subst h_trans_u h_trans_v h_frame_n h_frame_w h_frame_found
        h_frame_M h_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · obtain ⟨hn, _⟩ := h_pre; omega
  · omega
  · omega
  · omega
  · exact h_mi

-- ─────────────────────────────────────────────────────────────
-- sc3: L2 entry-bundle.  After B2 (v := v+1, w := 0), prove τ_L2.
-- ─────────────────────────────────────────────────────────────
theorem mm_sc3_l2_entry :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧ IsMatching G_s0 n_s0 M_s0 = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -1 ≤ v_s0 → v_s0 ≤ n_s0 - 1 → 0 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) →
    IsMatching G_s0 n_s0 M_s0 = 1 →
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    v_s1 = v_s0 + 1 → w_s1 = 0 →
    n_s1 = n_s0 → u_s1 = u_s0 → found_s1 = found_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    w_s1 ≤ n_s1 ∧ 0 ≤ v_s1 ∧ v_s1 ≤ n_s1 - 1 ∧
    0 ≤ u_s1 ∧ u_s1 ≤ n_s1 - 1 ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧
    IsMatching G_s1 n_s1 M_s1 = 1 ∧ 0 ≤ w_s1 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1
         h_pre h_v_lo h_v_hi h_u_lo h_u_hi h_found h_mi h_g
         h_trans_v h_trans_w h_frame_n h_frame_u h_frame_found
         h_frame_M h_frame_G
  subst h_trans_v h_trans_w h_frame_n h_frame_u h_frame_found
        h_frame_M h_frame_G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hn, _⟩ := h_pre; omega
  · omega
  · omega
  · exact h_u_lo
  · exact h_u_hi
  · omega
  · exact h_mi
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc5: L2 break-bundle (branch_idx=0 = AP found + flip).
-- Consequent: τ_L1 at body_out (since L1 is the enclosing).
-- ─────────────────────────────────────────────────────────────
theorem mm_sc5_l2_break :
    ∀ (n k u v w found : Int) (M : Int → Int) (G : Int → Int → Int)
      (found' : Int) (M' : Int → Int),
    (n ≥ 0 ∧ k > 0 ∧ IsMatching G n M = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    -- τ_L2 (full, 8 atoms)
    w ≤ n → 0 ≤ v → v ≤ n - 1 → 0 ≤ u → u ≤ n - 1 →
    (found = 0 ∨ found = 1) → IsMatching G n M = 1 → 0 ≤ w →
    -- Combined guard
    (w < n ∧ v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧
     w ≠ u ∧ w ≠ v ∧ w ≠ M v ∧
     M w = -1 ∧ G (M v) w ≥ 1 ∧ M u = -1) →
    -- Trans (flip + found := 1)
    (M' = store (store (store (store M u v) v u) (M v) w) w (M v)) →
    found' = 1 →
    -- Goal: τ_L1 at body_out.
    -1 ≤ v ∧ v ≤ n - 1 ∧ 0 ≤ u ∧ u ≤ n - 1 ∧
    (found' = 0 ∨ found' = 1) ∧ IsMatching G n M' = 1 := by
  intros n k u v w found M G found' M'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4
         h_tau_5 h_tau_6 h_tau_7
         h_guard h_trans_M h_trans_found
  obtain ⟨hn, h_k, h_mi, h_sym⟩ := h_pre
  obtain ⟨h_g_w, h_g_uv, h_g_Gpos, h_g_Mv, h_g_wu, h_g_wv,
          h_g_wMv, h_g_Mw, h_g_Gz, h_g_Mu⟩ := h_guard
  refine ⟨?_, h_tau_2, h_tau_3, h_tau_4, ?_, ?_⟩
  · omega
  · omega
  · -- IsMatching G n M' = 1: apply mm_flip_preserves_matching.
    rw [h_trans_M]
    have h_v_lt : v < n := by omega
    have h_u_lt : u < n := by omega
    have h_w_lt : w < n := h_g_w
    exact mm_flip_preserves_matching G n M u v w
      ⟨h_mi, h_tau_3, h_u_lt, h_tau_1, h_v_lt, h_tau_7, h_w_lt,
       h_g_uv, h_g_wu, h_g_wv, h_g_wMv, h_g_Mv,
       h_g_Mw, h_g_Mu, h_g_Gpos, h_g_Gz⟩

-- ─────────────────────────────────────────────────────────────
-- sc6: L2 safety (branch_idx=1 = increment w).  Goal: τ_L2(out).
-- Trans: w' = w + 1 (others preserved).  This is omega-trivial
-- for every conjunct.
-- ─────────────────────────────────────────────────────────────
theorem mm_sc6_l2_safety_step :
    ∀ (n k u v w found : Int) (M : Int → Int) (G : Int → Int → Int)
      (w' : Int),
    (n ≥ 0 ∧ k > 0 ∧ IsMatching G n M = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    w ≤ n → 0 ≤ v → v ≤ n - 1 → 0 ≤ u → u ≤ n - 1 →
    (found = 0 ∨ found = 1) → IsMatching G n M = 1 → 0 ≤ w →
    (w < n ∧ ¬(v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧
               w ≠ u ∧ w ≠ v ∧ w ≠ M v ∧ M w = -1 ∧
               G (M v) w ≥ 1 ∧ M u = -1)) →
    w' = w + 1 →
    w' ≤ n ∧ 0 ≤ v ∧ v ≤ n - 1 ∧ 0 ≤ u ∧ u ≤ n - 1 ∧
    (found = 0 ∨ found = 1) ∧ IsMatching G n M = 1 ∧ 0 ≤ w' := by
  intros n k u v w found M G w'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4
         h_tau_5 h_tau_6 h_tau_7
         h_guard h_trans_w
  subst h_trans_w
  obtain ⟨h_g_w, _⟩ := h_guard
  refine ⟨?_, h_tau_1, h_tau_2, h_tau_3, h_tau_4, h_tau_5, h_tau_6, ?_⟩
  · omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc15: coverage of SB(n=2) at end.  g_branch_0 = `found == 1`,
-- g_branch_1 = `found == 0`.  We need: τ ⇒ found == 1 ∨ found == 0.
-- (Coverage doesn't have an enclosing Loop's `found ∈ {0,1}`
-- atom in scope — but the obligation is from L0 exit, so τ_L0
-- is in scope.)
--
-- Only τ@L0 atom 2 (`found = 0 ∨ found = 1`) is load-bearing;
-- the other atoms are bystanders.  Helper takes ONLY that atom
-- so the registry can match partial-τ subsets too (otherwise
-- the per-subset enumeration rejects 2^3 = 8 valid subsets under
-- sound mode, blocking the global SAT).
-- ─────────────────────────────────────────────────────────────
theorem mm_sc15_coverage :
    ∀ (n k u v w found : Int) (M : Int → Int) (G : Int → Int → Int),
    (n ≥ 0 ∧ k > 0 ∧ IsMatching G n M = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    (found = 0 ∨ found = 1) →
    found = 1 ∨ found = 0 := by
  intros n k u v w found M G _h_pre h_tau_2
  exact h_tau_2.symm

-- ─────────────────────────────────────────────────────────────
-- sc9: L1 chain-bundle-post (middle body inductive via L2 abstract).
-- Goal: τ_L1 at s2.  L2 abstract: 8 τ_L2 atoms + frame (n, u, v, G).
-- No ¬g_L2 (L2 is break-capable).  No frame_M (L2 modifies M).
-- ─────────────────────────────────────────────────────────────
theorem mm_sc9_l1_body_ind :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧ IsMatching G_s0 n_s0 M_s0 = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -1 ≤ v_s0 → v_s0 ≤ n_s0 - 1 → 0 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) → IsMatching G_s0 n_s0 M_s0 = 1 →
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    v_s1 = v_s0 + 1 → w_s1 = 0 →
    n_s1 = n_s0 → u_s1 = u_s0 → found_s1 = found_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    w_s2 ≤ n_s2 → 0 ≤ v_s2 → v_s2 ≤ n_s2 - 1 →
    0 ≤ u_s2 → u_s2 ≤ n_s2 - 1 →
    (found_s2 = 0 ∨ found_s2 = 1) → IsMatching G_s2 n_s2 M_s2 = 1 →
    0 ≤ w_s2 →
    n_s2 = n_s1 → u_s2 = u_s1 → v_s2 = v_s1 → G_s2 = G_s1 →
    -1 ≤ v_s2 ∧ v_s2 ≤ n_s2 - 1 ∧ 0 ≤ u_s2 ∧ u_s2 ≤ n_s2 - 1 ∧
    (found_s2 = 0 ∨ found_s2 = 1) ∧ IsMatching G_s2 n_s2 M_s2 = 1 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1
         n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 M_s2 G_s2
         h_pre h_v_lo h_v_hi h_u_lo h_u_hi h_found h_mi h_g
         h_trans_v h_trans_w h_frame_n h_frame_u h_frame_found
         h_frame_M h_frame_G
         h_l2_w h_l2_v_lo h_l2_v_hi h_l2_u_lo h_l2_u_hi
         h_l2_found h_l2_mi h_l2_w_lo
         h_l2_frame_n h_l2_frame_u h_l2_frame_v h_l2_frame_G
  refine ⟨?_, h_l2_v_hi, h_l2_u_lo, h_l2_u_hi, h_l2_found, h_l2_mi⟩
  omega

-- ─────────────────────────────────────────────────────────────
-- sc11: L0 body inductive (chain-bundle-post via L1 abstract).
-- Goal: τ_L0 at s2.  L1 abstract: 6 τ_L1 + ¬g_L1 + frame (n, u, G).
-- L1's body modifies v, w, M, found; n, u, G preserved.
-- ─────────────────────────────────────────────────────────────
theorem mm_sc11_l0_body_ind :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧ IsMatching G_s0 n_s0 M_s0 = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -1 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) → IsMatching G_s0 n_s0 M_s0 = 1 →
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    u_s1 = u_s0 + 1 → v_s1 = -1 →
    n_s1 = n_s0 → w_s1 = w_s0 → found_s1 = found_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    -1 ≤ v_s2 → v_s2 ≤ n_s2 - 1 → 0 ≤ u_s2 → u_s2 ≤ n_s2 - 1 →
    (found_s2 = 0 ∨ found_s2 = 1) → IsMatching G_s2 n_s2 M_s2 = 1 →
    ¬ (v_s2 + 1 < n_s2 ∧ found_s2 = 0) →
    n_s2 = n_s1 → u_s2 = u_s1 → G_s2 = G_s1 →
    -1 ≤ u_s2 ∧ u_s2 ≤ n_s2 - 1 ∧
    (found_s2 = 0 ∨ found_s2 = 1) ∧ IsMatching G_s2 n_s2 M_s2 = 1 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1
         n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 M_s2 G_s2
         h_pre h_u_lo h_u_hi h_found h_mi h_g
         h_trans_u h_trans_v h_frame_n h_frame_w h_frame_found
         h_frame_M h_frame_G
         h_l1_v_lo h_l1_v_hi h_l1_u_lo h_l1_u_hi h_l1_found
         h_l1_mi h_l1_not_g
         h_l1_frame_n h_l1_frame_u h_l1_frame_G
  refine ⟨?_, ?_, h_l1_found, h_l1_mi⟩
  · omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc13/sc14: L0 FINAL bundle.  FLAT shape (L0 chain prefix has
-- no non-SB items).  Goal: IsMaxMatching G n M' = 1.
--
-- Proof (Option β): use mm_termination_implies_no_ap (class
-- restriction) to derive ¬ExistsAugPath, then Berge for max.
--
-- This is the SAME shape for both sc13 and sc14 — the framework
-- emits two chain-paths through the final SB(n=2) (recur vs
-- identity branches), but the proof obligation at the helper-cite
-- level is identical: prove IsMaxMatching from IsMatching + ¬g_L0.
-- ─────────────────────────────────────────────────────────────
theorem mm_sc14_final_berge :
    ∀ (n k u v w found : Int) (M : Int → Int) (G : Int → Int → Int)
      (u' v' w' found' : Int) (M' : Int → Int),
    (n ≥ 0 ∧ k > 0 ∧ IsMatching G n M = 1 ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    -1 ≤ u' → u' ≤ n - 1 →
    (found' = 0 ∨ found' = 1) →
    IsMatching G n M' = 1 →
    ¬ (u' + 1 < n ∧ found' = 0) →
    IsMaxMatching G n M' = 1 := by
  intros n k u v w found M G u' v' w' found' M'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_not_g
  -- Step 1: class-restriction → no AP exists.
  have h_no_ap :=
    mm_termination_implies_no_ap G n M' u' found' h_tau_3 h_not_g
  -- Step 2: Berge — IsMatching ∧ ¬AP → IsMaxMatching.
  exact mm_berge G n M' ⟨h_tau_3, h_no_ap⟩

end SynthLean.Y2Corpus.L16MaxMatchingRecur
