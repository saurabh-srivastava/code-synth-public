/-
Scratch proof: Slice 2.C's flip-preserves-IsMatching theorem.

Strategy: prove four pointwise lemmas about M' at the four
"flipped" indices {u, v, z, w} where z := M v, then case-split
the main proof on kk = u / v / z / w / otherwise.
-/
import SynthLean.Basic
open SynthLean

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
  -- Establish key facts about z := M v.
  obtain ⟨hz_lo, hz_hi⟩ : 0 ≤ M v ∧ M v < n :=
    hM_range v ⟨hv_lo, hv_hi, hMv_ne⟩
  have hMz_eq_v : M (M v) = v := hM_symm v ⟨hv_lo, hv_hi, hMv_ne⟩
  have hz_ne_u : M v ≠ u := by
    intro heq
    have : M u = v := by rw [← heq]; exact hMz_eq_v
    rw [hMu_eq] at this
    omega
  have hz_ne_v : M v ≠ v := hM_noself v ⟨hv_lo, hv_hi, hMv_ne⟩
  -- Pointwise values of M' at u, v, z=M v, w.
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
  -- Pointwise value for kk ∉ {u, v, M v, w}: M' kk = M kk.
  have hM'_other : ∀ kk : Int, kk ≠ u → kk ≠ v → kk ≠ M v → kk ≠ w →
      (store (store (store (store M u v) v u) (M v) w) w (M v)) kk = M kk := by
    intros kk hku hkv hkz hkw
    simp [store, hku, hkv, hkz, hkw]
  -- Now refine into four conjuncts.
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Range.
  · intro kk hkk; obtain ⟨hkk_lo, hkk_hi, hkk_ne⟩ := hkk
    by_cases hku : kk = u
    · rw [hku, hM'_u]; exact ⟨hv_lo, hv_hi⟩
    by_cases hkv : kk = v
    · rw [hkv, hM'_v]; exact ⟨hu_lo, hu_hi⟩
    by_cases hkz : kk = M v
    · rw [hkz, hM'_z]; exact ⟨hw_lo, hw_hi⟩
    by_cases hkw : kk = w
    · rw [hkw, hM'_w]; exact ⟨hz_lo, hz_hi⟩
    -- Otherwise.
    rw [hM'_other kk hku hkv hkz hkw]
    apply hM_range
    refine ⟨hkk_lo, hkk_hi, ?_⟩
    rw [hM'_other kk hku hkv hkz hkw] at hkk_ne
    exact hkk_ne
  -- Symm.
  · intro kk hkk; obtain ⟨hkk_lo, hkk_hi, hkk_ne⟩ := hkk
    by_cases hku : kk = u
    · rw [hku, hM'_u, hM'_v]
    by_cases hkv : kk = v
    · rw [hkv, hM'_v, hM'_u]
    by_cases hkz : kk = M v
    · rw [hkz, hM'_z, hM'_w]
    by_cases hkw : kk = w
    · rw [hkw, hM'_w, hM'_z]
    -- Otherwise: M' kk = M kk; need to show M kk ∉ {u, v, z, w}.
    rw [hM'_other kk hku hkv hkz hkw] at hkk_ne ⊢
    -- Now M kk ≠ -1 from hkk_ne (since M' kk = M kk).
    have hMkk_ne : M kk ≠ -1 := hkk_ne
    -- M kk = u? Then M (M kk) = M u = -1, but M_symm gives kk = -1; kk ≥ 0, contradicts unless...
    have hMkk_ne_u : M kk ≠ u := by
      intro heq
      have : M (M kk) = -1 := by rw [heq]; exact hMu_eq
      have hsym := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      omega
    -- M kk = v? Then M (M kk) = M v = z = some [0,n).  kk = z by M_symm.
    -- But kk ≠ M v means kk ≠ z, so kk ≠ z is hkz.  Substitute z = kk: contradicts hkz.
    have hMkk_ne_v : M kk ≠ v := by
      intro heq
      have h1 : M (M kk) = M v := by rw [heq]
      have h2 : M (M kk) = kk := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      -- So kk = M v.  But hkz says kk ≠ M v.
      exact hkz (by rw [← h2, h1])
    -- M kk = z?  Then M (M kk) = M z = v.  But M_symm says M (M kk) = kk, so kk = v.  Contradicts hkv.
    have hMkk_ne_z : M kk ≠ M v := by
      intro heq
      have h1 : M (M kk) = M (M v) := by rw [heq]
      rw [hMz_eq_v] at h1
      have h2 : M (M kk) = kk := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      exact hkv (by rw [← h2, h1])
    -- M kk = w?  Then M (M kk) = M w = -1.  kk = -1 by M_symm.  Contradicts.
    have hMkk_ne_w : M kk ≠ w := by
      intro heq
      have : M (M kk) = -1 := by rw [heq]; exact hMw_eq
      have hsym := hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
      omega
    rw [hM'_other (M kk) hMkk_ne_u hMkk_ne_v hMkk_ne_z hMkk_ne_w]
    exact hM_symm kk ⟨hkk_lo, hkk_hi, hMkk_ne⟩
  -- No-self.
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
  -- Edge.
  · intro kk hkk; obtain ⟨hkk_lo, hkk_hi, hkk_ne⟩ := hkk
    by_cases hku : kk = u
    · rw [hku, hM'_u]; exact huv_edge
    by_cases hkv : kk = v
    · rw [hkv, hM'_v]
      -- Goal: G v u ≥ 1; use G symm to get from G u v.
      rw [hG_symm v u ⟨hv_lo, hv_hi, hu_lo, hu_hi⟩]
      exact huv_edge
    by_cases hkz : kk = M v
    · rw [hkz, hM'_z]; exact hMv_w_edge
    by_cases hkw : kk = w
    · rw [hkw, hM'_w]
      -- Goal: G w (M v) ≥ 1; G symm + hMv_w_edge.
      rw [hG_symm w (M v) ⟨hw_lo, hw_hi, hz_lo, hz_hi⟩]
      exact hMv_w_edge
    rw [hM'_other kk hku hkv hkz hkw] at hkk_ne ⊢
    exact hM_edge kk ⟨hkk_lo, hkk_hi, hkk_ne⟩
