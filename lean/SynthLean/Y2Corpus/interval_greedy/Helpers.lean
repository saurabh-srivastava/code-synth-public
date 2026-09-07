/-
Interval-scheduling greedy-EDF Helpers — L1.6 breadth push (1/3).

Five Tier-1 helpers covering the 5 safety-class obligations
for `bench_interval_greedy.py`:
  - is_sc_entry_l0 : L0 entry-bundle after B0 init.
  - is_sc_accept   : L0 body safety, branch=0 (accept).
  - is_sc_skip     : L0 body safety, branch=1 (skip).
  - is_sc_coverage : L0 coverage (S[i] >= last_end ∨ S[i] < last_end).
  - is_sc_final    : L0 bundle-post (count = GreedyCount at exit).

UFs declared at file scope (must match the bench's
`emit_axiom_declarations` output for the cites to resolve).
Axioms declared in-namespace so they don't conflict with the
auto-emitted user_axiom_*.
-/
import SynthLean.Basic
open SynthLean

axiom GreedyCount   : (Int → Int) → (Int → Int) → Int → Int
axiom GreedyLastEnd : (Int → Int) → (Int → Int) → Int → Int

namespace SynthLean.Y2Corpus.IntervalGreedy

-- Local axioms (mirrors of the bench's user_axiom_0..5):
axiom greedy_count_base :
  ∀ (S E : Int → Int), GreedyCount S E 0 = 0
axiom greedy_last_end_base :
  ∀ (S E : Int → Int), GreedyLastEnd S E 0 = -1
axiom greedy_accept_count :
  ∀ (S E : Int → Int) (ii : Int),
    ii ≥ 0 ∧ S ii ≥ GreedyLastEnd S E ii →
    GreedyCount S E (ii + 1) = GreedyCount S E ii + 1
axiom greedy_accept_last_end :
  ∀ (S E : Int → Int) (ii : Int),
    ii ≥ 0 ∧ S ii ≥ GreedyLastEnd S E ii →
    GreedyLastEnd S E (ii + 1) = E ii
axiom greedy_skip_count :
  ∀ (S E : Int → Int) (ii : Int),
    ii ≥ 0 ∧ S ii < GreedyLastEnd S E ii →
    GreedyCount S E (ii + 1) = GreedyCount S E ii
axiom greedy_skip_last_end :
  ∀ (S E : Int → Int) (ii : Int),
    ii ≥ 0 ∧ S ii < GreedyLastEnd S E ii →
    GreedyLastEnd S E (ii + 1) = GreedyLastEnd S E ii

-- ─────────────────────────────────────────────────────────────
-- sc0: bundle-entry L0.  After B0 init, prove τ_L0 at exit state.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem is_sc_entry_l0 :
    ∀ (S E : Int → Int) (n count i last_end : Int)
      (count' i' last_end' : Int),
    (n ≥ 0 ∧
     (∀ (k1 k2 : Int), (0 ≤ k1 ∧ k1 < k2 ∧ k2 < n) → E k1 ≤ E k2) ∧
     (∀ (k : Int), (0 ≤ k ∧ k < n) → 0 ≤ S k ∧ S k < E k)) →
    i' = 0 → count' = 0 → last_end' = (0 - 1) →
    (0 ≤ i') ∧ (i' ≤ n) ∧ (0 ≤ count') ∧
    (count' = GreedyCount S E i') ∧
    (last_end' = GreedyLastEnd S E i') := by
  intros S E n count i last_end count' i' last_end' h_pre
         h_init_i h_init_count h_init_last_end
  subst h_init_i h_init_count h_init_last_end
  obtain ⟨hn, _, _⟩ := h_pre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · rw [greedy_count_base]
  · rw [greedy_last_end_base]; omega

-- ─────────────────────────────────────────────────────────────
-- sc1: coverage L0.  τ_L0 ∧ g_L0 ⇒ disj of branch guards.
-- Branches are S[i] >= last_end and S[i] < last_end — tautology.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem is_sc_coverage :
    ∀ (S E : Int → Int) (n count i last_end : Int),
    (n ≥ 0 ∧
     (∀ (k1 k2 : Int), (0 ≤ k1 ∧ k1 < k2 ∧ k2 < n) → E k1 ≤ E k2) ∧
     (∀ (k : Int), (0 ≤ k ∧ k < n) → 0 ≤ S k ∧ S k < E k)) →
    (i < n) →
    (S i ≥ last_end) ∨ (S i < last_end) := by
  intros S E n count i last_end h_pre h_g_loop
  by_cases h : S i ≥ last_end
  · exact Or.inl h
  · right; omega

-- ─────────────────────────────────────────────────────────────
-- sc2: L0 body safety, branch=0 (accept).
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem is_sc_accept :
    ∀ (S E : Int → Int) (n count i last_end : Int)
      (count' i' last_end' : Int),
    (n ≥ 0 ∧
     (∀ (k1 k2 : Int), (0 ≤ k1 ∧ k1 < k2 ∧ k2 < n) → E k1 ≤ E k2) ∧
     (∀ (k : Int), (0 ≤ k ∧ k < n) → 0 ≤ S k ∧ S k < E k)) →
    0 ≤ i → i ≤ n → 0 ≤ count →
    count = GreedyCount S E i →
    last_end = GreedyLastEnd S E i →
    (i < n ∧ S i ≥ last_end) →
    last_end' = E i → count' = count + 1 → i' = i + 1 →
    (0 ≤ i') ∧ (i' ≤ n) ∧ (0 ≤ count') ∧
    (count' = GreedyCount S E i') ∧
    (last_end' = GreedyLastEnd S E i') := by
  intros S E n count i last_end count' i' last_end'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4
         h_guard h_trans_last_end h_trans_count h_trans_i
  obtain ⟨h_g_in, h_g_cond⟩ := h_guard
  subst h_trans_i h_trans_count h_trans_last_end
  -- S i ≥ GreedyLastEnd S E i from h_tau_4 + h_g_cond.
  have h_accept : i ≥ 0 ∧ S i ≥ GreedyLastEnd S E i := by
    refine ⟨h_tau_0, ?_⟩
    rw [← h_tau_4]; exact h_g_cond
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · -- count + 1 = GreedyCount S E (i + 1)
    have := greedy_accept_count S E i h_accept
    omega
  · -- E i = GreedyLastEnd S E (i + 1)
    have := greedy_accept_last_end S E i h_accept
    omega

-- ─────────────────────────────────────────────────────────────
-- sc4: L0 body safety, branch=1 (skip).
-- Note: count' and last_end' are NOT in the binder list because
-- B1.1 only modifies i.  The goal uses bare count/last_end.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem is_sc_skip :
    ∀ (S E : Int → Int) (n count i last_end : Int) (i' : Int),
    (n ≥ 0 ∧
     (∀ (k1 k2 : Int), (0 ≤ k1 ∧ k1 < k2 ∧ k2 < n) → E k1 ≤ E k2) ∧
     (∀ (k : Int), (0 ≤ k ∧ k < n) → 0 ≤ S k ∧ S k < E k)) →
    0 ≤ i → i ≤ n → 0 ≤ count →
    count = GreedyCount S E i →
    last_end = GreedyLastEnd S E i →
    (i < n ∧ S i < last_end) →
    i' = i + 1 →
    (0 ≤ i') ∧ (i' ≤ n) ∧ (0 ≤ count) ∧
    (count = GreedyCount S E i') ∧
    (last_end = GreedyLastEnd S E i') := by
  intros S E n count i last_end i'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4
         h_guard h_trans_i
  obtain ⟨h_g_in, h_g_cond⟩ := h_guard
  subst h_trans_i
  have h_skip : i ≥ 0 ∧ S i < GreedyLastEnd S E i := by
    refine ⟨h_tau_0, ?_⟩
    rw [← h_tau_4]; exact h_g_cond
  refine ⟨?_, ?_, h_tau_2, ?_, ?_⟩
  · omega
  · omega
  · -- count = GreedyCount S E (i + 1)
    have := greedy_skip_count S E i h_skip
    omega
  · -- last_end = GreedyLastEnd S E (i + 1)
    have := greedy_skip_last_end S E i h_skip
    omega

-- ─────────────────────────────────────────────────────────────
-- sc7: L0 bundle-post.  τ_L0 at exit ∧ ¬g_L0 ⇒ count' = GreedyCount(n).
-- ¬g says i' ≥ n; τ atom says i' ≤ n.  So i' = n.
-- Then h_tau_3 (count' = GreedyCount S E i') gives the goal.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem is_sc_final :
    ∀ (S E : Int → Int) (n count i last_end : Int)
      (count' i' last_end' : Int),
    (n ≥ 0 ∧
     (∀ (k1 k2 : Int), (0 ≤ k1 ∧ k1 < k2 ∧ k2 < n) → E k1 ≤ E k2) ∧
     (∀ (k : Int), (0 ≤ k ∧ k < n) → 0 ≤ S k ∧ S k < E k)) →
    0 ≤ i' → i' ≤ n → 0 ≤ count' →
    count' = GreedyCount S E i' →
    last_end' = GreedyLastEnd S E i' →
    ¬ (i' < n) →
    count' = GreedyCount S E n := by
  intros S E n count i last_end count' i' last_end'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_not_g
  have h_i_eq : i' = n := by omega
  rw [h_tau_3, h_i_eq]

end SynthLean.Y2Corpus.IntervalGreedy
