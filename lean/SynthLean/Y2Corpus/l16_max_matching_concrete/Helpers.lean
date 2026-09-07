/-
Slice 2.C Helpers — max matching with CONCRETE IsMatching atoms.

Tier-1 theorems (proven from first principles):
  - flip_preserves_im: the 4-store AP-flip preserves the 4-atom
    concrete IsMatching predicate (replaces Slice 2.B's
    `mm_flip_preserves_matching` axiom).
  - mm_sc2..mm_sc15: 8 helper theorems for the chain-bundle
    obligations.  Each destructures the 4 concrete IsMatching
    atoms (range/symm/no_self/edge) and threads them through the
    chain frames + transitions.

Axioms (KEPT from Slice 2.B; rewritten to use concrete predicate):
  - mm_berge: Berge's theorem; takes 4 concrete IM atoms + ¬AP.
  - mm_termination_implies_no_ap: class-restriction axiom.
-/
import SynthLean.Basic
open SynthLean

axiom IsMaxMatching : (Int → Int → Int) → Int → (Int → Int) → Int
axiom ExistsAugPath : (Int → Int → Int) → Int → (Int → Int) → Int

namespace SynthLean.Y2Corpus.L16MaxMatchingConcrete

-- ─── Axioms ────────────────────────────────────────────────────

axiom mm_berge :
  ∀ (G_mat : Int → Int → Int) (m_n : Int) (M_arr : Int → Int),
    ((∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       0 ≤ M_arr kk ∧ M_arr kk < m_n) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       M_arr (M_arr kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       M_arr kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       G_mat kk (M_arr kk) ≥ 1) ∧
     ExistsAugPath G_mat m_n M_arr = 0) →
    IsMaxMatching G_mat m_n M_arr = 1

axiom mm_termination_implies_no_ap :
  ∀ (G_mat : Int → Int → Int) (m_n : Int) (M_arr : Int → Int)
    (m_u_prime m_found_prime : Int),
    (∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       0 ≤ M_arr kk ∧ M_arr kk < m_n) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       M_arr (M_arr kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       M_arr kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < m_n ∧ M_arr kk ≠ -1) →
       G_mat kk (M_arr kk) ≥ 1) →
    ¬ (m_u_prime + 1 < m_n ∧ m_found_prime = 0) →
    ExistsAugPath G_mat m_n M_arr = 0

-- ─── Tier-1 Theorem: flip preserves IsMatching ────────────────

set_option linter.unusedVariables false in
theorem flip_preserves_im :
    ∀ (G : Int → Int → Int) (n : Int) (M : Int → Int)
      (u v w : Int),
    n ≥ 0 →
    0 ≤ u → u < n → 0 ≤ v → v < n → 0 ≤ w → w < n →
    v ≠ u → w ≠ u → w ≠ v → w ≠ M v →
    M v ≠ -1 → M w = -1 → M u = -1 →
    G u v ≥ 1 → G (M v) w ≥ 1 →
    (∀ p q : Int, (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) → G p q = G q p) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       0 ≤ M kk ∧ M kk < n) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M (M kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       G kk (M kk) ≥ 1) →
    let M' := store (store (store (store M u v) v u) (M v) w) w (M v)
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       0 ≤ M' kk ∧ M' kk < n) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       M' (M' kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       M' kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       G kk (M' kk) ≥ 1) := by
  intros G n M u v w hn hu_lo hu_hi hv_lo hv_hi hw_lo hw_hi
         hvu hwu hwv hwMv hMv_ne hMw_eq hMu_eq
         huv_edge hMv_w_edge hG_symm
         hM_range hM_symm hM_noself hM_edge
  obtain ⟨hz_lo, hz_hi⟩ : 0 ≤ M v ∧ M v < n :=
    hM_range v ⟨hv_lo, hv_hi, hMv_ne⟩
  have hMz_eq_v : M (M v) = v := hM_symm v ⟨hv_lo, hv_hi, hMv_ne⟩
  have hz_ne_u : M v ≠ u := by
    intro heq
    have : M u = v := by rw [← heq]; exact hMz_eq_v
    rw [hMu_eq] at this
    omega
  have hz_ne_v : M v ≠ v := hM_noself v ⟨hv_lo, hv_hi, hMv_ne⟩
  have hM'_u : (store (store (store (store M u v) v u) (M v) w) w (M v)) u = v := by
    simp [store, show u ≠ w from hwu.symm,
          show u ≠ M v from hz_ne_u.symm,
          show u ≠ v from hvu.symm]
  have hM'_v : (store (store (store (store M u v) v u) (M v) w) w (M v)) v = u := by
    simp [store, show v ≠ w from hwv.symm,
          show v ≠ M v from hz_ne_v.symm]
  have hM'_z : (store (store (store (store M u v) v u) (M v) w) w (M v)) (M v) = w := by
    simp [store, show M v ≠ w from hwMv.symm]
  have hM'_w : (store (store (store (store M u v) v u) (M v) w) w (M v)) w = M v := by
    simp [store]
  have hM'_other : ∀ kk : Int, kk ≠ u → kk ≠ v → kk ≠ M v → kk ≠ w →
      (store (store (store (store M u v) v u) (M v) w) w (M v)) kk = M kk := by
    intros kk hku hkv hkz hkw
    simp [store, hku, hkv, hkz, hkw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro kk hkk; obtain ⟨hkk_lo, hkk_hi, hkk_ne⟩ := hkk
    by_cases hku : kk = u
    · rw [hku, hM'_u]; exact ⟨hv_lo, hv_hi⟩
    by_cases hkv : kk = v
    · rw [hkv, hM'_v]; exact ⟨hu_lo, hu_hi⟩
    by_cases hkz : kk = M v
    · rw [hkz, hM'_z]; exact ⟨hw_lo, hw_hi⟩
    by_cases hkw : kk = w
    · rw [hkw, hM'_w]; exact ⟨hz_lo, hz_hi⟩
    rw [hM'_other kk hku hkv hkz hkw]
    apply hM_range
    refine ⟨hkk_lo, hkk_hi, ?_⟩
    rw [hM'_other kk hku hkv hkz hkw] at hkk_ne
    exact hkk_ne
  · intro kk hkk; obtain ⟨hkk_lo, hkk_hi, hkk_ne⟩ := hkk
    by_cases hku : kk = u
    · rw [hku, hM'_u, hM'_v]
    by_cases hkv : kk = v
    · rw [hkv, hM'_v, hM'_u]
    by_cases hkz : kk = M v
    · rw [hkz, hM'_z, hM'_w]
    by_cases hkw : kk = w
    · rw [hkw, hM'_w, hM'_z]
    rw [hM'_other kk hku hkv hkz hkw] at hkk_ne ⊢
    have hMkk_ne : M kk ≠ -1 := hkk_ne
    have hMkk_ne_u : M kk ≠ u := by
      intro heq
      have : M (M kk) = -1 := by rw [heq]; exact hMu_eq
      have hsym := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      omega
    have hMkk_ne_v : M kk ≠ v := by
      intro heq
      have h1 : M (M kk) = M v := by rw [heq]
      have h2 : M (M kk) = kk := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      exact hkz (by rw [← h2, h1])
    have hMkk_ne_z : M kk ≠ M v := by
      intro heq
      have h1 : M (M kk) = M (M v) := by rw [heq]
      rw [hMz_eq_v] at h1
      have h2 : M (M kk) = kk := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      exact hkv (by rw [← h2, h1])
    have hMkk_ne_w : M kk ≠ w := by
      intro heq
      have : M (M kk) = -1 := by rw [heq]; exact hMw_eq
      have hsym := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      omega
    rw [hM'_other (M kk) hMkk_ne_u hMkk_ne_v hMkk_ne_z hMkk_ne_w]
    exact hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
  · intro kk hkk; obtain ⟨hkk_lo, hkk_hi, hkk_ne⟩ := hkk
    by_cases hku : kk = u
    · rw [hku, hM'_u]; exact hvu
    by_cases hkv : kk = v
    · rw [hkv, hM'_v]; exact hvu.symm
    by_cases hkz : kk = M v
    · rw [hkz, hM'_z]; exact hwMv
    by_cases hkw : kk = w
    · rw [hkw, hM'_w]; exact hwMv.symm
    rw [hM'_other kk hku hkv hkz hkw] at hkk_ne ⊢
    exact hM_noself kk ⟨hkk_lo, hkk_hi, hkk_ne⟩
  · intro kk hkk; obtain ⟨hkk_lo, hkk_hi, hkk_ne⟩ := hkk
    by_cases hku : kk = u
    · rw [hku, hM'_u]; exact huv_edge
    by_cases hkv : kk = v
    · rw [hkv, hM'_v]
      rw [hG_symm v u ⟨hv_lo, hv_hi, hu_lo, hu_hi⟩]
      exact huv_edge
    by_cases hkz : kk = M v
    · rw [hkz, hM'_z]; exact hMv_w_edge
    by_cases hkw : kk = w
    · rw [hkw, hM'_w]
      rw [hG_symm w (M v) ⟨hw_lo, hw_hi, hz_lo, hz_hi⟩]
      exact hMv_w_edge
    rw [hM'_other kk hku hkv hkz hkw] at hkk_ne ⊢
    exact hM_edge kk ⟨hkk_lo, hkk_hi, hkk_ne⟩

-- ─── Helper TIER-1 Theorems (9 helpers — sc1 added) ──────────

-- ─────────────────────────────────────────────────────────────
-- sc1: L0 entry-bundle.  FLAT shape (bare pre-state + primed
-- post-state for B0-modified vars only).
-- B0 sets: found=0, u=-1, v=-1, w=0, c=0; M, G, n, k unchanged.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc1_l0_entry :
    ∀ (n k u v w found c : Int)
      (M : Int → Int) (G : Int → Int → Int)
      (u' v' w' found' c' : Int),
    (n ≥ 0 ∧ k > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        0 ≤ M kk ∧ M kk < n) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M (M kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        G kk (M kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    found' = 0 → u' = (0 - 1) → v' = (0 - 1) →
    w' = 0 → c' = 0 →
    -- Goal: τ@L0 at exit (8 atoms; M, G, n unchanged).
    (0 - 1) ≤ u' ∧ u' ≤ n - 1 ∧
    (found' = 0 ∨ found' = 1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       0 ≤ M kk ∧ M kk < n) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M (M kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       G kk (M kk) ≥ 1) ∧
    c' ≥ 0 := by
  intros n k u v w found c M G u' v' w' found' c'
         h_pre h_init_found h_init_u h_init_v h_init_w h_init_c
  subst h_init_found h_init_u h_init_v h_init_w h_init_c
  obtain ⟨hn, _, h_range, h_symm, h_noself, h_edge, _⟩ := h_pre
  refine ⟨?_, ?_, ?_, h_range, h_symm, h_noself, h_edge, ?_⟩
  · omega
  · omega
  · left; rfl
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc2: L1 entry-bundle.  After B1 (u := u+1, v := -1), prove τ_L1.
-- τ@L0 enc (8 atoms): -1≤u, u≤n-1, found∈{0,1}, 4 IM atoms, c≥0.
-- τ@L1 (10 atoms): -1≤v, v≤n-1, 0≤u, u≤n-1, found∈{0,1},
--                  4 IM atoms, c≥0.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc2_l1_entry :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    -- h_pre: 7-conjunct.
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 (M_s0 kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        G_s0 kk (M_s0 kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -- τ@L0 atoms at s_0:
    -1 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 (M_s0 kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       G_s0 kk (M_s0 kk) ≥ 1) →
    c_s0 ≥ 0 →
    -- guard:
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- transitions:
    u_s1 = u_s0 + 1 → v_s1 = -1 →
    -- frames:
    n_s1 = n_s0 → w_s1 = w_s0 → found_s1 = found_s0 → c_s1 = c_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    -- Goal: τ@L1 atoms at s_1.
    -1 ≤ v_s1 ∧ v_s1 ≤ n_s1 - 1 ∧
    0 ≤ u_s1 ∧ u_s1 ≤ n_s1 - 1 ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       0 ≤ M_s1 kk ∧ M_s1 kk < n_s1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       M_s1 (M_s1 kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       M_s1 kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       G_s1 kk (M_s1 kk) ≥ 1) ∧
    c_s1 ≥ 0 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1
         h_pre h_tau_0 h_tau_1 h_tau_2
         h_tau_range h_tau_symm h_tau_noself h_tau_edge h_tau_c
         h_g h_trans_u h_trans_v
         h_frame_n h_frame_w h_frame_found h_frame_c h_frame_M h_frame_G
  subst h_trans_u h_trans_v h_frame_n h_frame_w h_frame_found
        h_frame_c h_frame_M h_frame_G
  obtain ⟨hn, _⟩ := h_pre
  refine ⟨?_, ?_, ?_, ?_, h_tau_2, h_tau_range, h_tau_symm,
          h_tau_noself, h_tau_edge, h_tau_c⟩
  · omega
  · omega
  · omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc3: L2 entry-bundle.  After B2 (v := v+1, w := 0), prove τ_L2.
-- τ@L1 enc (10 atoms); τ@L2 (12 atoms).
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc3_l2_entry :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int),
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 (M_s0 kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        G_s0 kk (M_s0 kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -- τ@L1 atoms (10): -1≤v, v≤n-1, 0≤u, u≤n-1, found∈{0,1},
    --                  range, symm, no_self, edge, c≥0.
    -1 ≤ v_s0 → v_s0 ≤ n_s0 - 1 →
    0 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 (M_s0 kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       G_s0 kk (M_s0 kk) ≥ 1) →
    c_s0 ≥ 0 →
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    v_s1 = v_s0 + 1 → w_s1 = 0 →
    n_s1 = n_s0 → u_s1 = u_s0 → found_s1 = found_s0 → c_s1 = c_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    -- Goal: τ@L2 atoms (12) at s_1.
    w_s1 ≤ n_s1 ∧
    0 ≤ v_s1 ∧ v_s1 ≤ n_s1 - 1 ∧
    0 ≤ u_s1 ∧ u_s1 ≤ n_s1 - 1 ∧
    (found_s1 = 0 ∨ found_s1 = 1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       0 ≤ M_s1 kk ∧ M_s1 kk < n_s1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       M_s1 (M_s1 kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       M_s1 kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s1 ∧ M_s1 kk ≠ -1) →
       G_s1 kk (M_s1 kk) ≥ 1) ∧
    0 ≤ w_s1 ∧
    c_s1 ≥ 0 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1
         h_pre h_tau_0 h_tau_1 h_u_lo h_u_hi h_tau_4
         h_tau_range h_tau_symm h_tau_noself h_tau_edge h_tau_c
         h_g h_trans_v h_trans_w
         h_frame_n h_frame_u h_frame_found h_frame_c h_frame_M h_frame_G
  subst h_trans_v h_trans_w h_frame_n h_frame_u h_frame_found
        h_frame_c h_frame_M h_frame_G
  obtain ⟨hn, _⟩ := h_pre
  refine ⟨?_, ?_, ?_, h_u_lo, h_u_hi, h_tau_4,
          h_tau_range, h_tau_symm, h_tau_noself, h_tau_edge, ?_, h_tau_c⟩
  · omega
  · omega
  · omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc5: L2 break-bundle (branch_idx=0).  AP found, flip + break.
-- Consequent: τ_L1 at body_out (L1 is enclosing).
-- Cites flip_preserves_im for the 4 IsMatching atoms at M'.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc5_l2_break :
    ∀ (n k u v w found c : Int) (M : Int → Int) (G : Int → Int → Int)
      (found' c' : Int) (M' : Int → Int),
    (n ≥ 0 ∧ k > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        0 ≤ M kk ∧ M kk < n) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M (M kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        G kk (M kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    -- τ@L2 (12 atoms):
    w ≤ n → 0 ≤ v → v ≤ n - 1 → 0 ≤ u → u ≤ n - 1 →
    (found = 0 ∨ found = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       0 ≤ M kk ∧ M kk < n) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M (M kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       G kk (M kk) ≥ 1) →
    0 ≤ w → c ≥ 0 →
    -- Combined guard.
    (w < n ∧ v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧
     w ≠ u ∧ w ≠ v ∧ w ≠ M v ∧
     M w = -1 ∧ G (M v) w ≥ 1 ∧ M u = -1) →
    -- Transitions.
    (M' = store (store (store (store M u v) v u) (M v) w) w (M v)) →
    found' = 1 →
    c' = c + 2 →
    -- Goal: τ_L1 atoms at body_out (10 atoms).
    -1 ≤ v ∧ v ≤ n - 1 ∧
    0 ≤ u ∧ u ≤ n - 1 ∧
    (found' = 0 ∨ found' = 1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       0 ≤ M' kk ∧ M' kk < n) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       M' (M' kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       M' kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       G kk (M' kk) ≥ 1) ∧
    c' ≥ 0 := by
  intros n k u v w found c M G found' c' M'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5
         h_tau_range h_tau_symm h_tau_noself h_tau_edge
         h_tau_10 h_tau_c
         h_guard h_trans_M h_trans_found h_trans_c
  obtain ⟨hn, h_k, _, _, _, _, h_sym⟩ := h_pre
  obtain ⟨h_g_w, h_g_uv, h_g_Gpos, h_g_Mv, h_g_wu, h_g_wv,
          h_g_wMv, h_g_Mw, h_g_Gz, h_g_Mu⟩ := h_guard
  -- Apply flip_preserves_im to get the 4 IM atoms at M'.
  have h_v_lt : v < n := by omega
  have h_u_lt : u < n := by omega
  have h_w_lt : w < n := h_g_w
  have h_flip := flip_preserves_im G n M u v w
                   hn h_tau_3 h_u_lt h_tau_1 h_v_lt h_tau_10 h_w_lt
                   h_g_uv h_g_wu h_g_wv h_g_wMv h_g_Mv h_g_Mw h_g_Mu
                   h_g_Gpos h_g_Gz h_sym
                   h_tau_range h_tau_symm h_tau_noself h_tau_edge
  rw [h_trans_M]
  obtain ⟨h_M'_range, h_M'_symm, h_M'_noself, h_M'_edge⟩ := h_flip
  refine ⟨?_, ?_, ?_, ?_, ?_, h_M'_range, h_M'_symm, h_M'_noself,
          h_M'_edge, ?_⟩
  · omega
  · omega
  · exact h_tau_3
  · omega
  · omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc6: L2 safety (branch_idx=1).  Increment w.  Goal: τ_L2(out).
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc6_l2_safety_step :
    ∀ (n k u v w found c : Int) (M : Int → Int) (G : Int → Int → Int)
      (w' : Int),
    (n ≥ 0 ∧ k > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        0 ≤ M kk ∧ M kk < n) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M (M kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        G kk (M kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    w ≤ n → 0 ≤ v → v ≤ n - 1 → 0 ≤ u → u ≤ n - 1 →
    (found = 0 ∨ found = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       0 ≤ M kk ∧ M kk < n) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M (M kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       G kk (M kk) ≥ 1) →
    0 ≤ w → c ≥ 0 →
    -- Guard (branch=1): w < n ∧ ¬AP_cond.
    (w < n ∧ ¬ (v ≠ u ∧ G u v ≥ 1 ∧ M v ≠ -1 ∧
                w ≠ u ∧ w ≠ v ∧ w ≠ M v ∧
                M w = -1 ∧ G (M v) w ≥ 1 ∧ M u = -1)) →
    w' = w + 1 →
    -- Goal: τ_L2 at w' (12 atoms).  Other vars unchanged.
    w' ≤ n ∧
    0 ≤ v ∧ v ≤ n - 1 ∧ 0 ≤ u ∧ u ≤ n - 1 ∧
    (found = 0 ∨ found = 1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       0 ≤ M kk ∧ M kk < n) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M (M kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       M kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
       G kk (M kk) ≥ 1) ∧
    0 ≤ w' ∧
    c ≥ 0 := by
  intros n k u v w found c M G w'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5
         h_tau_range h_tau_symm h_tau_noself h_tau_edge
         h_tau_10 h_tau_c h_guard h_trans_w
  subst h_trans_w
  refine ⟨?_, h_tau_1, h_tau_2, h_tau_3, h_tau_4, h_tau_5,
          h_tau_range, h_tau_symm, h_tau_noself, h_tau_edge, ?_, h_tau_c⟩
  · obtain ⟨h_g_w, _⟩ := h_guard; omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc9: L1 chain-bundle-post (middle body inductive via L2 abstract).
-- Same shape as Slice 2.B but with c_s* binders + 4 IM atoms.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc9_l1_body_ind :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 c_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 (M_s0 kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        G_s0 kk (M_s0 kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -- τ@L1 enc (10): -1≤v, v≤n-1, 0≤u, u≤n-1, found∈{0,1}, range, symm, no_self, edge, c≥0.
    -1 ≤ v_s0 → v_s0 ≤ n_s0 - 1 →
    0 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 (M_s0 kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       G_s0 kk (M_s0 kk) ≥ 1) →
    c_s0 ≥ 0 →
    (v_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    -- B2 transitions + frame.
    v_s1 = v_s0 + 1 → w_s1 = 0 →
    n_s1 = n_s0 → u_s1 = u_s0 → found_s1 = found_s0 → c_s1 = c_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    -- L2 abstract: τ_L2 at s2 (12 atoms).
    w_s2 ≤ n_s2 →
    0 ≤ v_s2 → v_s2 ≤ n_s2 - 1 →
    0 ≤ u_s2 → u_s2 ≤ n_s2 - 1 →
    (found_s2 = 0 ∨ found_s2 = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       0 ≤ M_s2 kk ∧ M_s2 kk < n_s2) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 (M_s2 kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       G_s2 kk (M_s2 kk) ≥ 1) →
    0 ≤ w_s2 → c_s2 ≥ 0 →
    -- L2 frames (skip M, since L2 modifies M via flip).
    n_s2 = n_s1 → u_s2 = u_s1 → v_s2 = v_s1 → G_s2 = G_s1 →
    -- Goal: τ@L1 at s2 (10 atoms).
    -1 ≤ v_s2 ∧ v_s2 ≤ n_s2 - 1 ∧
    0 ≤ u_s2 ∧ u_s2 ≤ n_s2 - 1 ∧
    (found_s2 = 0 ∨ found_s2 = 1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       0 ≤ M_s2 kk ∧ M_s2 kk < n_s2) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 (M_s2 kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       G_s2 kk (M_s2 kk) ≥ 1) ∧
    c_s2 ≥ 0 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1
         n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 c_s2 M_s2 G_s2
         h_pre _ _ _ _ _ _ _ _ _ _ _
         _ _ _ _ _ _ _ _
         _ _ _ _ _ h_L2_found
         h_L2_range h_L2_symm h_L2_noself h_L2_edge
         _ h_L2_c h_fr_n h_fr_u h_fr_v h_fr_G
  refine ⟨?_, ?_, ?_, ?_, h_L2_found, h_L2_range, h_L2_symm,
          h_L2_noself, h_L2_edge, h_L2_c⟩
  · omega
  · omega
  · omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc11: L0 chain-bundle-post (outer body inductive via L1 abstract).
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc11_l0_body_ind :
    ∀ (n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 : Int)
      (M_s0 : Int → Int) (G_s0 : Int → Int → Int)
      (n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 : Int)
      (M_s1 : Int → Int) (G_s1 : Int → Int → Int)
      (n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 c_s2 : Int)
      (M_s2 : Int → Int) (G_s2 : Int → Int → Int),
    (n_s0 ≥ 0 ∧ k_s0 > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 (M_s0 kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        M_s0 kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
        G_s0 kk (M_s0 kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n_s0 ∧ 0 ≤ q ∧ q < n_s0) →
       G_s0 p q = G_s0 q p) →
    -- τ@L0 (8): -1≤u, u≤n-1, found∈{0,1}, 4 IM, c≥0.
    -1 ≤ u_s0 → u_s0 ≤ n_s0 - 1 →
    (found_s0 = 0 ∨ found_s0 = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       0 ≤ M_s0 kk ∧ M_s0 kk < n_s0) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 (M_s0 kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       M_s0 kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s0 ∧ M_s0 kk ≠ -1) →
       G_s0 kk (M_s0 kk) ≥ 1) →
    c_s0 ≥ 0 →
    (u_s0 + 1 < n_s0 ∧ found_s0 = 0) →
    u_s1 = u_s0 + 1 → v_s1 = -1 →
    n_s1 = n_s0 → w_s1 = w_s0 → found_s1 = found_s0 → c_s1 = c_s0 →
    M_s1 = M_s0 → G_s1 = G_s0 →
    -- L1 abstract: τ_L1 at s2 (10) + ¬g_L1 at s2.
    -1 ≤ v_s2 → v_s2 ≤ n_s2 - 1 →
    0 ≤ u_s2 → u_s2 ≤ n_s2 - 1 →
    (found_s2 = 0 ∨ found_s2 = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       0 ≤ M_s2 kk ∧ M_s2 kk < n_s2) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 (M_s2 kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       G_s2 kk (M_s2 kk) ≥ 1) →
    c_s2 ≥ 0 →
    ¬ (v_s2 + 1 < n_s2 ∧ found_s2 = 0) →
    -- L1 frames (skip M; L1 modifies M via flip).
    n_s2 = n_s1 → u_s2 = u_s1 → G_s2 = G_s1 →
    -- Goal: τ@L0 at s2 (8 atoms).
    -1 ≤ u_s2 ∧ u_s2 ≤ n_s2 - 1 ∧
    (found_s2 = 0 ∨ found_s2 = 1) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       0 ≤ M_s2 kk ∧ M_s2 kk < n_s2) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 (M_s2 kk) = kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       M_s2 kk ≠ kk) ∧
    (∀ kk : Int, (0 ≤ kk ∧ kk < n_s2 ∧ M_s2 kk ≠ -1) →
       G_s2 kk (M_s2 kk) ≥ 1) ∧
    c_s2 ≥ 0 := by
  intros n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0
         n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1
         n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 c_s2 M_s2 G_s2
         h_pre _ _ _ _ _ _ _ _ _
         _ _ _ _ _ _ _ _
         _ _ h_L1_u_lo h_L1_u_hi h_L1_found
         h_L1_range h_L1_symm h_L1_noself h_L1_edge h_L1_c
         h_L1_not_g h_fr_n h_fr_u h_fr_G
  refine ⟨?_, ?_, h_L1_found, h_L1_range, h_L1_symm,
          h_L1_noself, h_L1_edge, h_L1_c⟩
  · omega
  · omega

-- ─────────────────────────────────────────────────────────────
-- sc14: L0 final / Berge.  τ_L0 + ¬g_L0 ⇒ IsMaxMatching.
-- Cites class-restriction axiom (¬AP) + Berge.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc14_final_berge :
    ∀ (n k u v w found c : Int) (M : Int → Int) (G : Int → Int → Int)
      (u' v' w' found' c' : Int) (M' : Int → Int),
    (n ≥ 0 ∧ k > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        0 ≤ M kk ∧ M kk < n) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M (M kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        G kk (M kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    -- τ@L0 (8) at exit state (primed): -1≤u', u'≤n-1, found'∈{0,1},
    --                                  4 IM atoms for M', c'≥0.
    -1 ≤ u' → u' ≤ n - 1 →
    (found' = 0 ∨ found' = 1) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       0 ≤ M' kk ∧ M' kk < n) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       M' (M' kk) = kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       M' kk ≠ kk) →
    (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M' kk ≠ -1) →
       G kk (M' kk) ≥ 1) →
    c' ≥ 0 →
    ¬ (u' + 1 < n ∧ found' = 0) →
    IsMaxMatching G n M' = 1 := by
  intros n k u v w found c M G u' v' w' found' c' M'
         h_pre h_tau_0 h_tau_1 h_tau_2
         h_M'_range h_M'_symm h_M'_noself h_M'_edge
         h_tau_c h_not_g
  have h_no_ap := mm_termination_implies_no_ap G n M' u' found'
    h_M'_range h_M'_symm h_M'_noself h_M'_edge h_not_g
  exact mm_berge G n M'
    ⟨h_M'_range, h_M'_symm, h_M'_noself, h_M'_edge, h_no_ap⟩

-- ─────────────────────────────────────────────────────────────
-- sc15: procedure-level coverage of final SB(n=2).  Need: found ∈ {0,1}.
-- Same as Slice 2.B's helper but bench has c local.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem mm_sc15_coverage :
    ∀ (n k u v w found c : Int) (M : Int → Int) (G : Int → Int → Int),
    (n ≥ 0 ∧ k > 0 ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        0 ≤ M kk ∧ M kk < n) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M (M kk) = kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        M kk ≠ kk) ∧
     (∀ kk : Int, (0 ≤ kk ∧ kk < n ∧ M kk ≠ -1) →
        G kk (M kk) ≥ 1) ∧
     ∀ (p q : Int), (0 ≤ p ∧ p < n ∧ 0 ≤ q ∧ q < n) →
       G p q = G q p) →
    (found = 0 ∨ found = 1) →
    found = 1 ∨ found = 0 := by
  intros n k u v w found c M G _h_pre h_found
  exact h_found.symm

end SynthLean.Y2Corpus.L16MaxMatchingConcrete
