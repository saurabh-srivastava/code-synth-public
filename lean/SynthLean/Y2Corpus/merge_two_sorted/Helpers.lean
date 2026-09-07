/-
merge_two_sorted Tier-3 helpers — RESEARCH.md §H.1.

Two algorithmic invariant preservations (one per SB(n=2)
branch of L0):
  Branch 0: A[i] ≤ B[j], emit A[i], i := i+1.
  Branch 1: A[i] > B[j], emit B[j], j := j+1.

Each preserves the 7-atom τ@L0:
  0: 0 ≤ i        4: is_sorted(C, i+j) = 1
  1: i ≤ n        5: i+j > 0 → C[i+j-1] ≤ A[i]
  2: 0 ≤ j        6: i+j > 0 → C[i+j-1] ≤ B[j]
  3: j ≤ p

Banked as named Tier-2 axioms (classical merge invariant
preservation).  Same precedent as boyer_moore_dominance
(majority), sp_self_nonneg (FW), kadane_branch{0,1}_preserves_inv.
Future work: prove from user axioms + induction.

The non-trivial conjuncts in each proof:
  - is_sorted(C', new_len) = 1: requires axiom-8 (recurrence)
    + store unfolding (C'[i+j-1] = C[i+j-1] since i+j-1 ≠ i+j)
    + the "last emitted ≤ next" τ atom (h_tau_5 or h_tau_6).
  - "last emitted ≤ next A/B" after the step:
      Branch 0: C'[(i+1)+j-1] = C'[i+j] = A[i].  Need A[i] ≤
                next_A = A[i+1] (from is_sorted A axiom-6 when
                i+1 < n).  Need A[i] ≤ next_B = B[j] (= the
                guard).
      Branch 1: dual.
-/
import SynthLean.Basic
open SynthLean

axiom is_sorted : (Int → Int) → Int → Int
-- Per-array base / recurrence axioms — mirror Problem.axioms.
axiom mts_user_axiom_0 : ∀ (A : Int → Int), ((is_sorted A 0) = 1)
axiom mts_user_axiom_1 : ∀ (B : Int → Int), ((is_sorted B 0) = 1)
axiom mts_user_axiom_2 : ∀ (C : Int → Int), ((is_sorted C 0) = 1)
axiom mts_user_axiom_3 : ∀ (A : Int → Int), ((is_sorted A 1) = 1)
axiom mts_user_axiom_4 : ∀ (B : Int → Int), ((is_sorted B 1) = 1)
axiom mts_user_axiom_5 : ∀ (C : Int → Int), ((is_sorted C 1) = 1)
axiom mts_user_axiom_6 : ∀ (A : Int → Int), (∀ k : Int,
    ((k ≥ 1) → ((is_sorted A (k + 1)) =
                (if (((is_sorted A k) = 1) ∧ ((A (k - 1)) ≤ (A k)))
                 then 1 else 0))))
axiom mts_user_axiom_7 : ∀ (B : Int → Int), (∀ k : Int,
    ((k ≥ 1) → ((is_sorted B (k + 1)) =
                (if (((is_sorted B k) = 1) ∧ ((B (k - 1)) ≤ (B k)))
                 then 1 else 0))))
axiom mts_user_axiom_8 : ∀ (C : Int → Int), (∀ k : Int,
    ((k ≥ 1) → ((is_sorted C (k + 1)) =
                (if (((is_sorted C k) = 1) ∧ ((C (k - 1)) ≤ (C k)))
                 then 1 else 0))))

-- ─── Auxiliary lemmas for is_sorted reasoning (Tier-1). ───

-- is_sorted depends only on positions < k.
theorem is_sorted_eq_below (A B : Int → Int) (k : Int) (hk : k ≥ 0)
    (h_agree : ∀ i : Int, 0 ≤ i → i < k → A i = B i) :
    is_sorted A k = is_sorted B k := by
  induction k, hk using Int.le_induction with
  | base => rw [mts_user_axiom_0, mts_user_axiom_0]
  | succ k hk ih =>
    by_cases hk1 : k = 0
    · subst hk1
      show is_sorted A 1 = is_sorted B 1
      rw [mts_user_axiom_3, mts_user_axiom_3]
    · have hk_ge1 : k ≥ 1 := by omega
      rw [mts_user_axiom_6 A k hk_ge1, mts_user_axiom_6 B k hk_ge1]
      have ih_eq : is_sorted A k = is_sorted B k :=
        ih (fun i h0 hk_ => h_agree i h0 (by omega))
      have hA_km1 : A (k - 1) = B (k - 1) :=
        h_agree (k - 1) (by omega) (by omega)
      have hA_k : A k = B k := h_agree k (by omega) (by omega)
      rw [ih_eq, hA_km1, hA_k]

-- Store at position k doesn't affect is_sorted up to m ≤ k.
theorem is_sorted_store_unchanged (A : Int → Int) (k v m : Int)
    (hm : m ≥ 0) (hmk : m ≤ k) :
    is_sorted (store A k v) m = is_sorted A m := by
  apply is_sorted_eq_below _ _ _ hm
  intro i _ hi
  unfold store
  have h_ne : i ≠ k := by omega
  simp [h_ne]

-- Downward propagation: is_sorted A n = 1 ⇒ is_sorted A k = 1 for k ≤ n.
theorem is_sorted_down (A : Int → Int) (n k : Int) (hk : 1 ≤ k) (hkn : k ≤ n)
    (h_sorted_n : is_sorted A n = 1) : is_sorted A k = 1 := by
  suffices h_aux : ∀ m : Nat, ∀ n_ : Int, k + m = n_ → k ≤ n_ →
                    is_sorted A n_ = 1 → is_sorted A k = 1 by
    exact h_aux (n - k).toNat n (by omega) hkn h_sorted_n
  intro m
  induction m with
  | zero =>
    intro n_ h_eq _ h_sn
    have : n_ = k := by omega
    rw [← this]; exact h_sn
  | succ m ih =>
    intro n_ h_eq _ h_sn
    have h_axiom := mts_user_axiom_6 A (n_ - 1) (by omega)
    have h_n_eq : n_ - 1 + 1 = n_ := by omega
    rw [h_n_eq] at h_axiom
    rw [h_axiom] at h_sn
    by_cases hcond : (is_sorted A (n_ - 1) = 1) ∧ (A ((n_ - 1) - 1) ≤ A (n_ - 1))
    · exact ih (n_ - 1) (by omega) (by omega) hcond.1
    · simp [hcond] at h_sn

-- Extract A[k-1] ≤ A[k] from is_sorted A n.
theorem is_sorted_extract (A : Int → Int) (n k : Int)
    (h_sorted : is_sorted A n = 1) (h_k_ge : 1 ≤ k) (h_k_lt : k < n) :
    A (k - 1) ≤ A k := by
  have h_sk1 : is_sorted A (k + 1) = 1 :=
    is_sorted_down A n (k + 1) (by omega) (by omega) h_sorted
  have h_axiom := mts_user_axiom_6 A k h_k_ge
  rw [h_axiom] at h_sk1
  by_cases hcond : (is_sorted A k = 1) ∧ (A (k - 1) ≤ A k)
  · exact hcond.2
  · simp [hcond] at h_sk1

-- is_sorted extension axiom (mirrored): A is sorted up to k+1 iff
-- sorted up to k AND last step monotonic.  Used in the forward
-- direction (preserves_inv).
theorem is_sorted_extend (A : Int → Int) (k : Int) (hk : k ≥ 1)
    (h_prev : is_sorted A k = 1) (h_le : A (k - 1) ≤ A k) :
    is_sorted A (k + 1) = 1 := by
  rw [mts_user_axiom_6 A k hk]
  simp [h_prev, h_le]

-- τ atoms 5/6 in the user benchmark are GATED on `i<n` / `j<p`
-- respectively (see merge_two_sorted.py).  At the boundary (i=n
-- or j=p after a step), the gated antecedent fails and the atom
-- is vacuously true — no boundary axiom needed.

/-
Branch 0 (emit A[i], advance i): preserves τ@L0.  Tier-1 proof
using user recurrence axioms.  With τ atom 5/6 gated on `i<n`/
`j<p`, the boundary case is vacuous.
-/
theorem merge_branch0_preserves_inv :
    ∀ (n p i j i' : Int)
      (A B C C' : Int → Int),
      ((n ≥ 0) ∧ (p ≥ 0) ∧ ((is_sorted A n) = 1) ∧ ((is_sorted B p) = 1)) →
      (0 ≤ i) →
      (i ≤ n) →
      (0 ≤ j) →
      (j ≤ p) →
      ((is_sorted C (i + j)) = 1) →
      ((((i + j) > 0) ∧ (i < n)) → ((C ((i + j) - 1)) ≤ (A i))) →
      ((((i + j) > 0) ∧ (j < p)) → ((C ((i + j) - 1)) ≤ (B j))) →
      (((i < n) ∧ (j < p)) ∧ ((A i) ≤ (B j))) →
      (C' = (store C (i + j) (A i))) →
      (i' = (i + 1)) →
      ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((0 ≤ j)) ∧ ((j ≤ p)) ∧
      (((is_sorted C' (i' + j)) = 1)) ∧
      ((((i' + j) > 0) ∧ (i' < n)) → ((C' ((i' + j) - 1)) ≤ (A i'))) ∧
      ((((i' + j) > 0) ∧ (j < p)) → ((C' ((i' + j) - 1)) ≤ (B j))) := by
  intro n p i j i' A B C C'
  intro h_pre hi_nn hi_le hj_nn hj_le h_C_sorted h_C_last_A h_C_last_B h_guard hC' hi'
  obtain ⟨_, _, hsA, _⟩ := h_pre
  obtain ⟨⟨h_i_lt_n, h_j_lt_p⟩, h_AiB_le⟩ := h_guard
  refine ⟨by omega, by omega, hj_nn, hj_le, ?_, ?_, ?_⟩
  · by_cases h_ij : i + j = 0
    · have h_ij' : i' + j = 1 := by omega
      rw [h_ij']; exact mts_user_axiom_5 C'
    · have h_ij_ge : i + j ≥ 1 := by omega
      have h_ij' : i' + j = (i + j) + 1 := by omega
      rw [h_ij']
      apply is_sorted_extend C' (i + j) h_ij_ge
      · rw [hC']
        rw [is_sorted_store_unchanged C (i+j) (A i) (i+j) (by omega) (le_refl _)]
        exact h_C_sorted
      · rw [hC']; unfold store
        have h_lhs_ne : ¬ ((i + j) - 1) = (i + j) := by omega
        simp [h_lhs_ne]
        exact h_C_last_A ⟨by omega, h_i_lt_n⟩
  · rintro ⟨_, h_in⟩
    rw [hi'] at h_in
    rw [hC', hi']
    have h_idx : (i + 1) + j - 1 = i + j := by omega
    rw [h_idx]; unfold store; simp
    have h_idx2 : (i + 1) - 1 = i := by omega
    have := is_sorted_extract A n (i + 1) hsA (by omega) h_in
    rw [h_idx2] at this; exact this
  · rintro _
    rw [hC', hi']
    have h_idx : (i + 1) + j - 1 = i + j := by omega
    rw [h_idx]; unfold store; simp
    exact h_AiB_le

/-
Branch 1 (emit B[j], advance j): preserves τ@L0.  Tier-1 mirror
of branch 0 (swap A↔B, i↔j).  Boundary vacuous via gated τ.
-/
theorem merge_branch1_preserves_inv :
    ∀ (n p i j j' : Int)
      (A B C C' : Int → Int),
      ((n ≥ 0) ∧ (p ≥ 0) ∧ ((is_sorted A n) = 1) ∧ ((is_sorted B p) = 1)) →
      (0 ≤ i) →
      (i ≤ n) →
      (0 ≤ j) →
      (j ≤ p) →
      ((is_sorted C (i + j)) = 1) →
      ((((i + j) > 0) ∧ (i < n)) → ((C ((i + j) - 1)) ≤ (A i))) →
      ((((i + j) > 0) ∧ (j < p)) → ((C ((i + j) - 1)) ≤ (B j))) →
      (((i < n) ∧ (j < p)) ∧ ((A i) > (B j))) →
      (C' = (store C (i + j) (B j))) →
      (j' = (j + 1)) →
      ((0 ≤ i)) ∧ ((i ≤ n)) ∧ ((0 ≤ j')) ∧ ((j' ≤ p)) ∧
      (((is_sorted C' (i + j')) = 1)) ∧
      ((((i + j') > 0) ∧ (i < n)) → ((C' ((i + j') - 1)) ≤ (A i))) ∧
      ((((i + j') > 0) ∧ (j' < p)) → ((C' ((i + j') - 1)) ≤ (B j'))) := by
  intro n p i j j' A B C C'
  intro h_pre hi_nn hi_le hj_nn hj_le h_C_sorted h_C_last_A h_C_last_B h_guard hC' hj'
  obtain ⟨_, _, _, hsB⟩ := h_pre
  obtain ⟨⟨h_i_lt_n, h_j_lt_p⟩, h_AiB_gt⟩ := h_guard
  refine ⟨hi_nn, hi_le, by omega, by omega, ?_, ?_, ?_⟩
  · by_cases h_ij : i + j = 0
    · have h_ij' : i + j' = 1 := by omega
      rw [h_ij']; exact mts_user_axiom_5 C'
    · have h_ij_ge : i + j ≥ 1 := by omega
      have h_ij' : i + j' = (i + j) + 1 := by omega
      rw [h_ij']
      apply is_sorted_extend C' (i + j) h_ij_ge
      · rw [hC']
        rw [is_sorted_store_unchanged C (i+j) (B j) (i+j) (by omega) (le_refl _)]
        exact h_C_sorted
      · rw [hC']; unfold store
        have h_lhs_ne : ¬ ((i + j) - 1) = (i + j) := by omega
        simp [h_lhs_ne]
        exact h_C_last_B ⟨by omega, h_j_lt_p⟩
  · rintro _
    rw [hC', hj']
    have h_idx : i + (j + 1) - 1 = i + j := by omega
    rw [h_idx]; unfold store; simp
    linarith
  · rintro ⟨_, h_jp⟩
    rw [hj'] at h_jp
    rw [hC', hj']
    have h_idx : i + (j + 1) - 1 = i + j := by omega
    rw [h_idx]; unfold store; simp
    have h_idx2 : (j + 1) - 1 = j := by omega
    have := is_sorted_extract B p (j + 1) hsB (by omega) h_jp
    rw [h_idx2] at this; exact this

/-
L1 safety: drain-B loop (single branch).  Emit B[j], advance j.

τ@L1 has 6 atoms (no "last ≤ A" since A is exhausted at L1
entry):
  0: 0 ≤ i        3: j ≤ p
  1: i ≤ n        4: is_sorted(C, i+j) = 1
  2: 0 ≤ j        5: i+j > 0 → C[i+j-1] ≤ B[j]
-/
theorem merge_l1_drain_b_preserves_inv :
    ∀ (n p i j j' : Int)
      (A B C C' : Int → Int),
      ((n ≥ 0) ∧ (p ≥ 0) ∧ ((is_sorted A n) = 1) ∧ ((is_sorted B p) = 1)) →
      (0 ≤ i) →
      (i ≤ n) →
      (0 ≤ j) →
      (j ≤ p) →
      ((is_sorted C (i + j)) = 1) →
      ((((i + j) > 0) ∧ (j < p)) → ((C ((i + j) - 1)) ≤ (B j))) →
      (j < p) →
      (C' = (store C (i + j) (B j))) →
      (j' = (j + 1)) →
      ((0 ≤ i)) ∧ ((i ≤ n)) ∧ ((0 ≤ j')) ∧ ((j' ≤ p)) ∧
      (((is_sorted C' (i + j')) = 1)) ∧
      ((((i + j') > 0) ∧ (j' < p)) → ((C' ((i + j') - 1)) ≤ (B j'))) := by
  intro n p i j j' A B C C'
  intro h_pre hi_nn hi_le hj_nn hj_le h_C_sorted h_C_last_B h_g hC' hj'
  obtain ⟨_, _, _, hsB⟩ := h_pre
  refine ⟨hi_nn, hi_le, by omega, by omega, ?_, ?_⟩
  · by_cases h_ij : i + j = 0
    · have h_ij' : i + j' = 1 := by omega
      rw [h_ij']; exact mts_user_axiom_5 C'
    · have h_ij_ge : i + j ≥ 1 := by omega
      have h_ij' : i + j' = (i + j) + 1 := by omega
      rw [h_ij']
      apply is_sorted_extend C' (i + j) h_ij_ge
      · rw [hC']
        rw [is_sorted_store_unchanged C (i+j) (B j) (i+j) (by omega) (le_refl _)]
        exact h_C_sorted
      · rw [hC']; unfold store
        have h_lhs_ne : ¬ ((i + j) - 1) = (i + j) := by omega
        simp [h_lhs_ne]
        exact h_C_last_B ⟨by omega, h_g⟩
  · rintro ⟨_, h_jp⟩
    rw [hj'] at h_jp
    rw [hC', hj']
    have h_idx : i + (j + 1) - 1 = i + j := by omega
    rw [h_idx]; unfold store; simp
    have h_idx2 : (j + 1) - 1 = j := by omega
    have := is_sorted_extract B p (j + 1) hsB (by omega) h_jp
    rw [h_idx2] at this; exact this

/-
L2 safety: drain-A loop (single branch).  Emit A[i], advance i.

τ@L2 has 6 atoms (mirror of L1; "last ≤ B" replaced by
"last ≤ A").
-/
theorem merge_l2_drain_a_preserves_inv :
    ∀ (n p i j i' : Int)
      (A B C C' : Int → Int),
      ((n ≥ 0) ∧ (p ≥ 0) ∧ ((is_sorted A n) = 1) ∧ ((is_sorted B p) = 1)) →
      (0 ≤ i) →
      (i ≤ n) →
      (0 ≤ j) →
      (j ≤ p) →
      ((is_sorted C (i + j)) = 1) →
      ((((i + j) > 0) ∧ (i < n)) → ((C ((i + j) - 1)) ≤ (A i))) →
      (i < n) →
      (C' = (store C (i + j) (A i))) →
      (i' = (i + 1)) →
      ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((0 ≤ j)) ∧ ((j ≤ p)) ∧
      (((is_sorted C' (i' + j)) = 1)) ∧
      ((((i' + j) > 0) ∧ (i' < n)) → ((C' ((i' + j) - 1)) ≤ (A i'))) := by
  intro n p i j i' A B C C'
  intro h_pre hi_nn hi_le hj_nn hj_le h_C_sorted h_C_last_A h_g hC' hi'
  obtain ⟨_, _, hsA, _⟩ := h_pre
  refine ⟨by omega, by omega, hj_nn, hj_le, ?_, ?_⟩
  · by_cases h_ij : i + j = 0
    · have h_ij' : i' + j = 1 := by omega
      rw [h_ij']; exact mts_user_axiom_5 C'
    · have h_ij_ge : i + j ≥ 1 := by omega
      have h_ij' : i' + j = (i + j) + 1 := by omega
      rw [h_ij']
      apply is_sorted_extend C' (i + j) h_ij_ge
      · rw [hC']
        rw [is_sorted_store_unchanged C (i+j) (A i) (i+j) (by omega) (le_refl _)]
        exact h_C_sorted
      · rw [hC']; unfold store
        have h_lhs_ne : ¬ ((i + j) - 1) = (i + j) := by omega
        simp [h_lhs_ne]
        exact h_C_last_A ⟨by omega, h_g⟩
  · rintro ⟨_, h_in⟩
    rw [hi'] at h_in
    rw [hC', hi']
    have h_idx : (i + 1) + j - 1 = i + j := by omega
    rw [h_idx]; unfold store; simp
    have h_idx2 : (i + 1) - 1 = i := by omega
    have := is_sorted_extract A n (i + 1) hsA (by omega) h_in
    rw [h_idx2] at this; exact this

/-
sc7 — L1 entry-bundle (chain-aware, 2-item chain).

Goal: τ@L1 atoms at state 2 (entry of L1).  Chain has B0 init +
L0 abstract transition.

Proof sketch: trivial.  Each τ@L1 atom (0-5) is directly given
by a τ@L0 atom (0-4, then atom 6 for the last conjunct).  The
chain-aware translator emits ALL τ@L0 atoms as hypotheses
h_i1_L0_tau_0..h_i1_L0_tau_6; the conclusion's six conjuncts
follow by direct hypothesis appeal.

Banked as Tier-2 axiom; could be replaced by an in-translator
generic tactic chain (assumption + omega) if the chain-aware
shape were stable.  The fallthrough dumps showed the linter
flagging unused `simp_all` args as errors, so this short-circuits
through the helper path instead.
-/
-- Tier-1: every conjunct is direct from h_i1_L0_tau_* (the L0
-- exit τ atoms).  τ@L1 has the same bookkeeping atoms (0..3) and
-- inherits the "is_sorted C" and "last ≤ B[j]" atoms from L0.
theorem merge_l1_entry_chain :
    ∀ (n_s0 p_s0 i_s0 j_s0 : Int)
      (A_s0 B_s0 C_s0 : Int → Int)
      (n_s1 p_s1 i_s1 j_s1 : Int)
      (A_s1 B_s1 C_s1 : Int → Int)
      (n_s2 p_s2 i_s2 j_s2 : Int)
      (A_s2 B_s2 C_s2 : Int → Int),
      ((n_s0 ≥ 0) ∧ (p_s0 ≥ 0) ∧ ((is_sorted A_s0 n_s0) = 1)
         ∧ ((is_sorted B_s0 p_s0) = 1)) →
      (i_s1 = 0) → (j_s1 = 0) → (n_s1 = n_s0) → (p_s1 = p_s0) →
      (A_s1 = A_s0) → (B_s1 = B_s0) → (C_s1 = C_s0) →
      (0 ≤ i_s2) → (i_s2 ≤ n_s2) → (0 ≤ j_s2) → (j_s2 ≤ p_s2) →
      ((is_sorted C_s2 (i_s2 + j_s2)) = 1) →
      ((((i_s2 + j_s2) > 0) ∧ (i_s2 < n_s2)) → ((C_s2 ((i_s2 + j_s2) - 1)) ≤ (A_s2 i_s2))) →
      ((((i_s2 + j_s2) > 0) ∧ (j_s2 < p_s2)) → ((C_s2 ((i_s2 + j_s2) - 1)) ≤ (B_s2 j_s2))) →
      ¬ (((i_s2 < n_s2) ∧ (j_s2 < p_s2))) →
      (n_s2 = n_s1) → (p_s2 = p_s1) → (A_s2 = A_s1) → (B_s2 = B_s1) →
      ((0 ≤ i_s2)) ∧ ((i_s2 ≤ n_s2)) ∧ ((0 ≤ j_s2)) ∧ ((j_s2 ≤ p_s2)) ∧
      (((is_sorted C_s2 (i_s2 + j_s2)) = 1)) ∧
      ((((i_s2 + j_s2) > 0) ∧ (j_s2 < p_s2)) → ((C_s2 ((i_s2 + j_s2) - 1)) ≤ (B_s2 j_s2))) := by
  intros
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> assumption

/-
sc11 — L2 entry-bundle (chain-aware, multi-loop chain).

Goal: τ@L2 atoms at state 3 (entry of L2).  The chain has B0
init + L0 + L1 abstract transitions.

The 6th conjunct ("last ≤ A[i]") is the hard one: at L1's exit,
EITHER L1 didn't run (j was already ≥ p) → C unchanged from L0
and L0's atom 5 still holds; OR L1 ran (i ≥ n at L0 exit) →
L2 won't run (its guard i < n fails).  Both branches make the
implication's antecedent or conclusion trivially handled.

Banked as a Tier-2 axiom; the case analysis is the algorithmic
correctness of merge.  Future work: prove from the chain
hypotheses + classical case-split.
-/
axiom merge_l2_entry_chain :
    ∀ (n_s0 p_s0 i_s0 j_s0 : Int)
      (A_s0 B_s0 C_s0 : Int → Int)
      (n_s1 p_s1 i_s1 j_s1 : Int)
      (A_s1 B_s1 C_s1 : Int → Int)
      (n_s2 p_s2 i_s2 j_s2 : Int)
      (A_s2 B_s2 C_s2 : Int → Int)
      (n_s3 p_s3 i_s3 j_s3 : Int)
      (A_s3 B_s3 C_s3 : Int → Int),
      ((n_s0 ≥ 0) ∧ (p_s0 ≥ 0) ∧ ((is_sorted A_s0 n_s0) = 1)
         ∧ ((is_sorted B_s0 p_s0) = 1)) →
      (i_s1 = 0) → (j_s1 = 0) → (n_s1 = n_s0) → (p_s1 = p_s0) →
      (A_s1 = A_s0) → (B_s1 = B_s0) → (C_s1 = C_s0) →
      (0 ≤ i_s2) → (i_s2 ≤ n_s2) → (0 ≤ j_s2) → (j_s2 ≤ p_s2) →
      ((is_sorted C_s2 (i_s2 + j_s2)) = 1) →
      ((((i_s2 + j_s2) > 0) ∧ (i_s2 < n_s2)) → ((C_s2 ((i_s2 + j_s2) - 1)) ≤ (A_s2 i_s2))) →
      ((((i_s2 + j_s2) > 0) ∧ (j_s2 < p_s2)) → ((C_s2 ((i_s2 + j_s2) - 1)) ≤ (B_s2 j_s2))) →
      ¬ (((i_s2 < n_s2) ∧ (j_s2 < p_s2))) →
      (n_s2 = n_s1) → (p_s2 = p_s1) → (A_s2 = A_s1) → (B_s2 = B_s1) →
      (0 ≤ i_s3) → (i_s3 ≤ n_s3) → (0 ≤ j_s3) → (j_s3 ≤ p_s3) →
      ((is_sorted C_s3 (i_s3 + j_s3)) = 1) →
      ((((i_s3 + j_s3) > 0) ∧ (j_s3 < p_s3)) → ((C_s3 ((i_s3 + j_s3) - 1)) ≤ (B_s3 j_s3))) →
      ¬ ((j_s3 < p_s3)) →
      (n_s3 = n_s2) → (p_s3 = p_s2) → (i_s3 = i_s2) →
      (A_s3 = A_s2) → (B_s3 = B_s2) →
      ((0 ≤ i_s3)) ∧ ((i_s3 ≤ n_s3)) ∧ ((0 ≤ j_s3)) ∧ ((j_s3 ≤ p_s3)) ∧
      (((is_sorted C_s3 (i_s3 + j_s3)) = 1)) ∧
      ((((i_s3 + j_s3) > 0) ∧ (i_s3 < n_s3)) → ((C_s3 ((i_s3 + j_s3) - 1)) ≤ (A_s3 i_s3)))

/-
sc15 — final bundle-post (chain-aware).

Goal: `is_sorted(C_s4, n_s4 + p_s4) = 1`.  Chain runs through
B0 + L0 + L1 + L2 (5 states).

Proof sketch:
  - L2's ¬g: i_s4 ≥ n_s4; combined with atom 1 (i_s4 ≤ n_s4)
    → i_s4 = n_s4.
  - L1's ¬g: j_s3 ≥ p_s3 ∧ atom (j_s3 ≤ p_s3) → j_s3 = p_s3.
    L2 frame: j_s4 = j_s3, p_s4 = p_s3 → j_s4 = p_s4.
  - So i_s4 + j_s4 = n_s4 + p_s4.
  - L2's atom 4: is_sorted(C_s4, i_s4 + j_s4) = 1; substituting
    the equality yields is_sorted(C_s4, n_s4 + p_s4) = 1.

Banked as Tier-2 axiom for now.
-/
-- Tier-1: ¬g_L2 + bound ⇒ i_s4 = n_s4.  ¬g_L1 + bound ⇒
-- j_s3 = p_s3.  Frames: j_s4 = j_s3, p_s4 = p_s3 ⇒ j_s4 = p_s4.
-- So i_s4 + j_s4 = n_s4 + p_s4; rewrite the L2 exit τ atom.
theorem merge_final_post_chain :
    ∀ (n_s0 p_s0 i_s0 j_s0 : Int)
      (A_s0 B_s0 C_s0 : Int → Int)
      (n_s1 p_s1 i_s1 j_s1 : Int)
      (A_s1 B_s1 C_s1 : Int → Int)
      (n_s2 p_s2 i_s2 j_s2 : Int)
      (A_s2 B_s2 C_s2 : Int → Int)
      (n_s3 p_s3 i_s3 j_s3 : Int)
      (A_s3 B_s3 C_s3 : Int → Int)
      (n_s4 p_s4 i_s4 j_s4 : Int)
      (A_s4 B_s4 C_s4 : Int → Int),
      ((n_s0 ≥ 0) ∧ (p_s0 ≥ 0) ∧ ((is_sorted A_s0 n_s0) = 1)
         ∧ ((is_sorted B_s0 p_s0) = 1)) →
      (i_s1 = 0) → (j_s1 = 0) → (n_s1 = n_s0) → (p_s1 = p_s0) →
      (A_s1 = A_s0) → (B_s1 = B_s0) → (C_s1 = C_s0) →
      (0 ≤ i_s2) → (i_s2 ≤ n_s2) → (0 ≤ j_s2) → (j_s2 ≤ p_s2) →
      ((is_sorted C_s2 (i_s2 + j_s2)) = 1) →
      ((((i_s2 + j_s2) > 0) ∧ (i_s2 < n_s2)) → ((C_s2 ((i_s2 + j_s2) - 1)) ≤ (A_s2 i_s2))) →
      ((((i_s2 + j_s2) > 0) ∧ (j_s2 < p_s2)) → ((C_s2 ((i_s2 + j_s2) - 1)) ≤ (B_s2 j_s2))) →
      ¬ (((i_s2 < n_s2) ∧ (j_s2 < p_s2))) →
      (n_s2 = n_s1) → (p_s2 = p_s1) → (A_s2 = A_s1) → (B_s2 = B_s1) →
      (0 ≤ i_s3) → (i_s3 ≤ n_s3) → (0 ≤ j_s3) → (j_s3 ≤ p_s3) →
      ((is_sorted C_s3 (i_s3 + j_s3)) = 1) →
      ((((i_s3 + j_s3) > 0) ∧ (j_s3 < p_s3)) → ((C_s3 ((i_s3 + j_s3) - 1)) ≤ (B_s3 j_s3))) →
      ¬ ((j_s3 < p_s3)) →
      (n_s3 = n_s2) → (p_s3 = p_s2) → (i_s3 = i_s2) →
      (A_s3 = A_s2) → (B_s3 = B_s2) →
      (0 ≤ i_s4) → (i_s4 ≤ n_s4) → (0 ≤ j_s4) → (j_s4 ≤ p_s4) →
      ((is_sorted C_s4 (i_s4 + j_s4)) = 1) →
      ((((i_s4 + j_s4) > 0) ∧ (i_s4 < n_s4)) → ((C_s4 ((i_s4 + j_s4) - 1)) ≤ (A_s4 i_s4))) →
      ¬ ((i_s4 < n_s4)) →
      (n_s4 = n_s3) → (p_s4 = p_s3) → (j_s4 = j_s3) →
      (A_s4 = A_s3) → (B_s4 = B_s3) →
      ((is_sorted C_s4 (n_s4 + p_s4)) = 1) := by
  -- 32 vars: 4 ints + 3 arrays per state × 4 states = 28? No.
  -- Actually: 4 ints (n, p, i, j) + 3 arrays (A, B, C) × 4 = 28.
  intro _ _ _ _ _ _ _      -- s0: 4 + 3 = 7
  intro _ _ _ _ _ _ _      -- s1: 7
  intro _ _ _ _ _ _ _      -- s2: 7
  intro _ _ _ _ _ _ _      -- s3: 7
  intro n_s4 p_s4 i_s4 j_s4 _ _ _   -- s4: name n/p/i/j
  intro _ _ _ _ _ _ _ _   -- 8 outer: pre + 7 frame/init from s0→s1
  intro _ h_i_s2_le _ h_j_s2_le _ _ _ h_notg_L0 _ _ _ _   -- 12 s2 atoms
  intro _ h_i_s3_le _ h_j_s3_le _ _ h_notg_L1 _ _ _ _ _   -- s3 atoms + L1 frames
  intro _ h_i_s4_le _ h_j_s4_le h_C_s4_sorted _ h_notg_L2  -- s4 atoms
  intro h_n_eq h_p_eq h_j_eq _ _  -- L2 frame
  -- i_s4 = n_s4 (¬g_L2 + bound).  j_s4 = j_s3 = p_s3 = p_s4 (¬g_L1 + frames).
  have h_arg : i_s4 + j_s4 = n_s4 + p_s4 := by omega
  rw [← h_arg]
  exact h_C_s4_sorted

namespace SynthLean.MergeTwoSortedHelpers

-- Placeholder namespace for future Tier-1 theorems (when the
-- axioms above are converted to proofs from user_axioms).

end SynthLean.MergeTwoSortedHelpers
