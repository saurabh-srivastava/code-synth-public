/-
C1 greedy-match sc2 full-τ inductive (branch 0: both endpoints
unmatched, pair them).  τ = {0 ≤ i, i ≤ m, MI(M), maximal(M, i)}.
Transition: M' = store(store M eu ev) ev eu;  i' = i + 1
where eu = edges(2*i), ev = edges(2*i+1).

Proof plan:
  - omega for the two arithmetic conjuncts.
  - MI(M') case-split on k ∈ {ev, eu, else}.
  - maximal(M', i+1):
      • j = i: M'(eu) = ev, and ev ≥ 0 ≠ -1.
      • j < i: extend h_tau_3 via "M[k]≠-1 → M'[k]≠-1".
-/
import SynthLean.Basic
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
theorem sc2_fallthrough
    (m n i : Int)
    (edges M : Int → Int)
    (i' : Int)
    (M' : Int → Int)
    (h_pre : ((n ≥ 0) ∧ (m ≥ 0) ∧ (∀ k : Int, (((0 ≤ k) ∧ (k < n)) → ((M k) = (-1)))) ∧ (∀ j : Int, (((0 ≤ j) ∧ (j < m)) → ((0 ≤ (edges (2 * j))) ∧ ((edges (2 * j)) < n) ∧ (0 ≤ (edges ((2 * j) + 1))) ∧ ((edges ((2 * j) + 1)) < n) ∧ ((edges (2 * j)) ≠ (edges ((2 * j) + 1))))))))
    (h_tau_0 : (0 ≤ i))
    (h_tau_1 : (i ≤ m))
    (h_tau_2 : (∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M k) ≠ (-1))) → ((0 ≤ (M k)) ∧ ((M k) < n)))))
    (h_tau_3 : (∀ j : Int, (((0 ≤ j) ∧ (j < i)) → (¬ (((M (edges (2 * j))) = (-1)) ∧ ((M (edges ((2 * j) + 1))) = (-1)))))))
    (h_guard : ((i < m) ∧ (((M (edges (2 * i))) = (-1)) ∧ ((M (edges ((2 * i) + 1))) = (-1)))))
    (h_trans_M : M' = (store (store M (edges (2 * i)) (edges ((2 * i) + 1))) (edges ((2 * i) + 1)) (edges (2 * i))))
    (h_trans_i : i' = (i + 1)) :
    ((0 ≤ i')) ∧ ((i' ≤ m)) ∧ ((∀ k : Int, (((0 ≤ k) ∧ (k < n) ∧ ((M' k) ≠ (-1))) → ((0 ≤ (M' k)) ∧ ((M' k) < n))))) ∧ ((∀ j : Int, (((0 ≤ j) ∧ (j < i')) → (¬ (((M' (edges (2 * j))) = (-1)) ∧ ((M' (edges ((2 * j) + 1))) = (-1))))))) := by
  obtain ⟨h_pre_n, h_pre_m, h_pre_init, h_pre_edges⟩ := h_pre
  obtain ⟨h_g_lt, h_g_unmatched⟩ := h_guard
  subst h_trans_M
  subst h_trans_i
  -- Local names for the current edge's endpoints.
  set eu := edges (2 * i) with heu_def
  set ev := edges (2 * i + 1) with hev_def
  -- Well-formedness for the current edge.
  have h_edge_i : 0 ≤ eu ∧ eu < n ∧ 0 ≤ ev ∧ ev < n ∧ eu ≠ ev := by
    have := h_pre_edges i ⟨h_tau_0, h_g_lt⟩
    -- The above gives 0 ≤ edges (2*i) etc.; rewrite for `2*i + 1 = 2*i+1`.
    simp only [show (2 * i + 1) = (2 * i + 1) from rfl] at this
    exact this
  obtain ⟨h_eu_ge, h_eu_lt, h_ev_ge, h_ev_lt, h_eu_ne_ev⟩ := h_edge_i
  -- Lemma: M extends to M' (matched vertices stay matched).
  have h_extend : ∀ k : Int,
      M k ≠ -1 → store (store M eu ev) ev eu k ≠ -1 := by
    intro k hk
    by_cases hk_ev : k = ev
    · -- M'[ev] = eu.  eu ≥ 0, so ≠ -1.
      simp [store, hk_ev]; omega
    · by_cases hk_eu : k = eu
      · -- M'[eu] = ev.  ev ≥ 0, so ≠ -1.
        simp [store, hk_eu, hk_ev]; omega
      · -- M' k = M k.
        simp [store, hk_eu, hk_ev]; exact hk
  refine ⟨by omega, by omega, ?_, ?_⟩
  -- ── Matching-invariant preserved.
  · intro k ⟨hk0, hkn, hkneq⟩
    by_cases hk_ev : k = ev
    · -- M'[ev] = eu; need 0 ≤ eu < n.
      have : store (store M eu ev) ev eu k = eu := by simp [store, hk_ev]
      rw [this]; exact ⟨h_eu_ge, h_eu_lt⟩
    · by_cases hk_eu : k = eu
      · have : store (store M eu ev) ev eu k = ev := by
          simp [store, hk_eu, hk_ev]
        rw [this]; exact ⟨h_ev_ge, h_ev_lt⟩
      · have hval : store (store M eu ev) ev eu k = M k := by
          simp [store, hk_eu, hk_ev]
        rw [hval] at hkneq ⊢
        exact h_tau_2 k ⟨hk0, hkn, hkneq⟩
  -- ── Maximal up to i+1 preserved.
  · intro j ⟨hj0, hji⟩
    intro ⟨h1, h2⟩
    by_cases hj_eq : j = i
    · -- j = i case: M'[edges(2i)] = M'[eu] = ev ≥ 0, but h1 says it's -1.
      subst hj_eq
      have : store (store M eu ev) ev eu eu = ev := by
        simp [store, h_eu_ne_ev]
      rw [this] at h1
      omega
    · -- j < i case: use h_tau_3 + h_extend.
      have hji_strict : j < i := by omega
      -- From h_tau_3: NOT BOTH M[edges(2j)] = -1 AND M[edges(2j+1)] = -1.
      have h_orig := h_tau_3 j ⟨hj0, hji_strict⟩
      apply h_orig
      -- Need: M[edges(2j)] = -1 ∧ M[edges(2j+1)] = -1.
      -- Have h1: M'[edges(2j)] = -1, h2: M'[edges(2j+1)] = -1.
      -- If M[edges(2j)] ≠ -1, then M'[edges(2j)] ≠ -1 by h_extend — contradicts h1.
      refine ⟨?_, ?_⟩
      · by_contra hne
        exact h_extend (edges (2 * j)) hne h1
      · by_contra hne
        exact h_extend (edges (2 * j + 1)) hne h2
end SynthLean.VerifyTmp
