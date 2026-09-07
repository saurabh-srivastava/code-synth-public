/-
Gale-Shapley Tier-1 Helpers — L1.6 breadth push (2/3).

Phase 3 of GS work: per-constraint helpers that cite the
12 step axioms.  Same pattern as Slice 2.C and interval_greedy.

This file is being built incrementally; helpers are added one
at a time as smoke tests on the bench reveal the translator-
emitted theorem shapes.
-/
import SynthLean.Basic
open SynthLean

axiom GSMate   : (Int → Int → Int) → (Int → Int → Int) → Int → Int → (Int → Int)
axiom GSWMate  : (Int → Int → Int) → (Int → Int → Int) → Int → Int → (Int → Int)
axiom GSNxt    : (Int → Int → Int) → (Int → Int → Int) → Int → Int → (Int → Int)

namespace SynthLean.Y2Corpus.GaleShapley

-- ─── Step axioms (mirrors of bench's user_axiom_* sequence) ──
-- Order matches `_AXIOMS` in bench_gale_shapley.py.

axiom gs_base_mate :
  ∀ (pref rank : Int → Int → Int) (n mm : Int),
    0 ≤ mm ∧ mm < n → GSMate pref rank n 0 mm = -1
axiom gs_base_wmate :
  ∀ (pref rank : Int → Int → Int) (n ww : Int),
    0 ≤ ww ∧ ww < n → GSWMate pref rank n 0 ww = -1
axiom gs_base_nxt :
  ∀ (pref rank : Int → Int → Int) (n mm : Int),
    0 ≤ mm ∧ mm < n → GSNxt pref rank n 0 mm = 0

-- ─── sc0: L0 entry-bundle ──────────────────────────────────
-- After B0 init (m_cur' := 0, k_left' := k_iter), prove τ@L0.
-- The eight conjuncts:
--   1. 0 ≤ k_left' = k_iter (from h_pre)
--   2. k_left' = k_iter ≤ k_iter (omega)
--   3. n ≥ 1 (from h_pre)
--   4. ∀ mm. mate[mm] = GSMate(...,k_iter - k_iter=0)[mm] = -1 by base axiom; mate[mm] = -1 from h_pre.
--   5. similar for wmate.
--   6. similar for nxt = 0.
--   7. 0 ≤ m_cur' = 0 (omega)
--   8. m_cur' = 0 < n (from h_pre n ≥ 1).
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem gs_sc0_entry_l0 :
    ∀ (n k_iter m_cur k_left : Int)
      (mate wmate nxt : Int → Int)
      (pref rank : Int → Int → Int)
      (m_cur' k_left' : Int),
    (n ≥ 1 ∧ k_iter ≥ 0 ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → mate mm = -1) ∧
     (∀ (ww : Int), (0 ≤ ww ∧ ww < n) → wmate ww = -1) ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → nxt mm = 0) ∧
     (∀ (mm jj : Int), (0 ≤ mm ∧ mm < n ∧ 0 ≤ jj ∧ jj < n) →
        0 ≤ pref mm jj ∧ pref mm jj < n) ∧
     (∀ (ww mm : Int), (0 ≤ ww ∧ ww < n ∧ 0 ≤ mm ∧ mm < n) →
        0 ≤ rank ww mm ∧ rank ww mm < n)) →
    m_cur' = 0 → k_left' = k_iter →
    (0 ≤ k_left') ∧ (k_left' ≤ k_iter) ∧ (n ≥ 1) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate mm = GSMate pref rank n (k_iter - k_left') mm) ∧
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate ww = GSWMate pref rank n (k_iter - k_left') ww) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt mm = GSNxt pref rank n (k_iter - k_left') mm) ∧
    (0 ≤ m_cur') ∧ (m_cur' < n) := by
  intros n k_iter m_cur k_left mate wmate nxt pref rank m_cur' k_left'
         h_pre h_init_m_cur h_init_k_left
  subst h_init_m_cur h_init_k_left
  -- After subst: m_cur' eliminated (→ 0), k_iter eliminated (→ k_left').
  obtain ⟨h_n_ge1, h_kleft_ge0, h_mate_init, h_wmate_init,
          h_nxt_init, _, _⟩ := h_pre
  refine ⟨?_, ?_, h_n_ge1, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_kleft_ge0
  · omega
  · -- mate mm = GSMate ... 0 mm.  Both sides equal -1.
    intro mm hmm
    rw [h_mate_init mm hmm]
    have : k_left' - k_left' = 0 := by omega
    rw [this]
    rw [gs_base_mate pref rank n mm hmm]
  · intro ww hww
    rw [h_wmate_init ww hww]
    have : k_left' - k_left' = 0 := by omega
    rw [this]
    rw [gs_base_wmate pref rank n ww hww]
  · intro mm hmm
    rw [h_nxt_init mm hmm]
    have : k_left' - k_left' = 0 := by omega
    rw [this]
    rw [gs_base_nxt pref rank n mm hmm]
  · omega
  · omega

-- ─── sc1: coverage of SB(n=3) loop body ─────────────────────
-- The 3-branch loop body's guards must cover all cases:
--   SKIP:   mate[m] ≠ -1 ∨ nxt[m] ≥ n.
--   ACCEPT: mate[m] = -1 ∧ nxt[m] < n ∧ (wmate[w] = -1 ∨ rank prefers m).
--   REJECT: mate[m] = -1 ∧ nxt[m] < n ∧ ¬(wmate[w] = -1 ∨ rank prefers m).
-- Trichotomy by-cases on the conditions.
-- ─────────────────────────────────────────────────────────────
set_option linter.unusedVariables false in
theorem gs_sc1_coverage :
    ∀ (n k_iter m_cur k_left : Int)
      (mate wmate nxt : Int → Int)
      (pref rank : Int → Int → Int),
    True →  -- h_pre (unused)
    (k_left > 0) →
    (mate m_cur ≠ -1 ∨ nxt m_cur ≥ n)
    ∨ (mate m_cur = -1 ∧ nxt m_cur < n ∧
       (wmate (pref m_cur (nxt m_cur)) = -1 ∨
        rank (pref m_cur (nxt m_cur)) m_cur <
        rank (pref m_cur (nxt m_cur)) (wmate (pref m_cur (nxt m_cur)))))
    ∨ (mate m_cur = -1 ∧ nxt m_cur < n ∧
       ¬(wmate (pref m_cur (nxt m_cur)) = -1 ∨
         rank (pref m_cur (nxt m_cur)) m_cur <
         rank (pref m_cur (nxt m_cur)) (wmate (pref m_cur (nxt m_cur))))) := by
  intros n k_iter m_cur k_left mate wmate nxt pref rank _ _
  by_cases h_mate : mate m_cur = -1
  · by_cases h_nxt : nxt m_cur < n
    · by_cases h_w : wmate (pref m_cur (nxt m_cur)) = -1 ∨
        rank (pref m_cur (nxt m_cur)) m_cur <
        rank (pref m_cur (nxt m_cur)) (wmate (pref m_cur (nxt m_cur)))
      · right; left; exact ⟨h_mate, h_nxt, h_w⟩
      · right; right; exact ⟨h_mate, h_nxt, h_w⟩
    · left; right; omega
  · left; left; exact h_mate


-- ─── Step axioms — full set ─────────────────────────────────

axiom gs_skip_mate :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    (GSMate pref rank n kk mm ≠ -1 ∨ GSNxt pref rank n kk mm ≥ n) →
    ∀ (mm2 : Int), 0 ≤ mm2 ∧ mm2 < n →
      GSMate pref rank n (kk + 1) mm2 = GSMate pref rank n kk mm2
axiom gs_skip_wmate :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    (GSMate pref rank n kk mm ≠ -1 ∨ GSNxt pref rank n kk mm ≥ n) →
    ∀ (ww : Int), 0 ≤ ww ∧ ww < n →
      GSWMate pref rank n (kk + 1) ww = GSWMate pref rank n kk ww
axiom gs_skip_nxt :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    (GSMate pref rank n kk mm ≠ -1 ∨ GSNxt pref rank n kk mm ≥ n) →
    ∀ (mm2 : Int), 0 ≤ mm2 ∧ mm2 < n →
      GSNxt pref rank n (kk + 1) mm2 = GSNxt pref rank n kk mm2

lemma mod_subtraction_bounds (a n : Int) (hn : n ≥ 1) (ha : a ≥ 0) :
    0 ≤ a - (a / n) * n ∧ a - (a / n) * n < n := by
  have h1 : a % n = a - n * (a / n) := Int.emod_def a n
  have h2 : a % n = a - (a / n) * n := by rw [h1]; ring
  rw [← h2]
  refine ⟨Int.emod_nonneg a (by omega), Int.emod_lt_of_pos a (by omega)⟩

-- ─── sc2: safety branch=0 (SKIP) ─────────────────────────────
set_option linter.unusedVariables false in
theorem gs_sc2_skip :
    ∀ (n k_iter m_cur k_left : Int)
      (mate wmate nxt : Int → Int)
      (pref rank : Int → Int → Int)
      (m_cur' k_left' : Int),
    (n ≥ 1 ∧ k_iter ≥ 0 ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → mate mm = -1) ∧
     (∀ (ww : Int), (0 ≤ ww ∧ ww < n) → wmate ww = -1) ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → nxt mm = 0) ∧
     (∀ (mm jj : Int), (0 ≤ mm ∧ mm < n ∧ 0 ≤ jj ∧ jj < n) →
        0 ≤ pref mm jj ∧ pref mm jj < n) ∧
     (∀ (ww mm : Int), (0 ≤ ww ∧ ww < n ∧ 0 ≤ mm ∧ mm < n) →
        0 ≤ rank ww mm ∧ rank ww mm < n)) →
    0 ≤ k_left → k_left ≤ k_iter → n ≥ 1 →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate mm = GSMate pref rank n (k_iter - k_left) mm) →
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate ww = GSWMate pref rank n (k_iter - k_left) ww) →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt mm = GSNxt pref rank n (k_iter - k_left) mm) →
    0 ≤ m_cur → m_cur < n →
    (k_left > 0 ∧ (mate m_cur ≠ -1 ∨ nxt m_cur ≥ n)) →
    m_cur' = ((m_cur + 1) - ((m_cur + 1) / n) * n) →
    k_left' = k_left - 1 →
    (0 ≤ k_left') ∧ (k_left' ≤ k_iter) ∧ (n ≥ 1) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate mm = GSMate pref rank n (k_iter - k_left') mm) ∧
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate ww = GSWMate pref rank n (k_iter - k_left') ww) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt mm = GSNxt pref rank n (k_iter - k_left') mm) ∧
    (0 ≤ m_cur') ∧ (m_cur' < n) := by
  intros n k_iter m_cur k_left mate wmate nxt pref rank m_cur' k_left'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5
         h_tau_6 h_tau_7 h_guard h_trans_m_cur h_trans_k_left
  obtain ⟨h_g_loop, h_skip_cond⟩ := h_guard
  have h_kk_ge : k_iter - k_left ≥ 0 := by omega
  have h_skip_pre :
      k_iter - k_left ≥ 0 ∧ 0 ≤ m_cur ∧ m_cur < n ∧
      (GSMate pref rank n (k_iter - k_left) m_cur ≠ -1 ∨
       GSNxt pref rank n (k_iter - k_left) m_cur ≥ n) := by
    refine ⟨h_kk_ge, h_tau_6, h_tau_7, ?_⟩
    have hm := h_tau_3 m_cur ⟨h_tau_6, h_tau_7⟩
    have hnx := h_tau_5 m_cur ⟨h_tau_6, h_tau_7⟩
    cases h_skip_cond with
    | inl h => left; rw [← hm]; exact h
    | inr h => right; rw [← hnx]; exact h
  have h_skip_m  := gs_skip_mate  pref rank n (k_iter - k_left) m_cur h_skip_pre
  have h_skip_w  := gs_skip_wmate pref rank n (k_iter - k_left) m_cur h_skip_pre
  have h_skip_nx := gs_skip_nxt   pref rank n (k_iter - k_left) m_cur h_skip_pre
  have h_arg : k_iter - k_left' = (k_iter - k_left) + 1 := by omega
  subst h_trans_m_cur h_trans_k_left
  refine ⟨?_, ?_, h_tau_2, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro mm hmm
    rw [h_arg]
    rw [h_skip_m mm hmm]
    exact h_tau_3 mm hmm
  · intro ww hww
    rw [h_arg]
    rw [h_skip_w ww hww]
    exact h_tau_4 ww hww
  · intro mm hmm
    rw [h_arg]
    rw [h_skip_nx mm hmm]
    exact h_tau_5 mm hmm
  · exact (mod_subtraction_bounds (m_cur + 1) n h_tau_2 (by omega)).1
  · exact (mod_subtraction_bounds (m_cur + 1) n h_tau_2 (by omega)).2

-- ─── Structural axiom: GSNxt non-negative ──────────────────

axiom gs_nxt_nonneg :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n →
      0 ≤ GSNxt pref rank n kk mm

-- ─── ACCEPT step axioms ────────────────────────────────────

axiom gs_accept_mate_at_mm :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
     rank (pref mm (GSNxt pref rank n kk mm)) mm <
     rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    GSMate pref rank n (kk + 1) mm = pref mm (GSNxt pref rank n kk mm)

axiom gs_accept_wmate_at_w :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
     rank (pref mm (GSNxt pref rank n kk mm)) mm <
     rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    GSWMate pref rank n (kk + 1) (pref mm (GSNxt pref rank n kk mm)) = mm

axiom gs_accept_nxt_at_mm :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
     rank (pref mm (GSNxt pref rank n kk mm)) mm <
     rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    GSNxt pref rank n (kk + 1) mm = GSNxt pref rank n kk mm + 1

axiom gs_accept_mate_other :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
     rank (pref mm (GSNxt pref rank n kk mm)) mm <
     rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    ∀ (mm2 : Int), 0 ≤ mm2 ∧ mm2 < n ∧ mm2 ≠ mm ∧
      mm2 ≠ GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) →
      GSMate pref rank n (kk + 1) mm2 = GSMate pref rank n kk mm2

axiom gs_accept_mate_displaced :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) ≠ -1 ∧
    rank (pref mm (GSNxt pref rank n kk mm)) mm <
    rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm))) →
    GSMate pref rank n (kk + 1) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm))) = -1

axiom gs_accept_wmate_other :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
     rank (pref mm (GSNxt pref rank n kk mm)) mm <
     rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    ∀ (ww : Int), 0 ≤ ww ∧ ww < n ∧ ww ≠ pref mm (GSNxt pref rank n kk mm) →
      GSWMate pref rank n (kk + 1) ww = GSWMate pref rank n kk ww

axiom gs_accept_nxt_other :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
     rank (pref mm (GSNxt pref rank n kk mm)) mm <
     rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    ∀ (mm2 : Int), 0 ≤ mm2 ∧ mm2 < n ∧ mm2 ≠ mm →
      GSNxt pref rank n (kk + 1) mm2 = GSNxt pref rank n kk mm2

-- ─── REJECT step axioms ────────────────────────────────────

axiom gs_reject_nxt_at_mm :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    ¬ (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
       rank (pref mm (GSNxt pref rank n kk mm)) mm <
       rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    GSNxt pref rank n (kk + 1) mm = GSNxt pref rank n kk mm + 1

axiom gs_reject_mate_all :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    ¬ (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
       rank (pref mm (GSNxt pref rank n kk mm)) mm <
       rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    ∀ (mm2 : Int), 0 ≤ mm2 ∧ mm2 < n →
      GSMate pref rank n (kk + 1) mm2 = GSMate pref rank n kk mm2

axiom gs_reject_wmate_all :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    ¬ (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
       rank (pref mm (GSNxt pref rank n kk mm)) mm <
       rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    ∀ (ww : Int), 0 ≤ ww ∧ ww < n →
      GSWMate pref rank n (kk + 1) ww = GSWMate pref rank n kk ww

axiom gs_reject_nxt_other :
  ∀ (pref rank : Int → Int → Int) (n kk mm : Int),
    kk ≥ 0 ∧ 0 ≤ mm ∧ mm < n ∧
    GSMate pref rank n kk mm = -1 ∧
    GSNxt pref rank n kk mm < n ∧
    ¬ (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)) = -1 ∨
       rank (pref mm (GSNxt pref rank n kk mm)) mm <
       rank (pref mm (GSNxt pref rank n kk mm)) (GSWMate pref rank n kk (pref mm (GSNxt pref rank n kk mm)))) →
    ∀ (mm2 : Int), 0 ≤ mm2 ∧ mm2 < n ∧ mm2 ≠ mm →
      GSNxt pref rank n (kk + 1) mm2 = GSNxt pref rank n kk mm2

-- ─── sc4: safety branch=1 (ACCEPT) ─────────────────────────
set_option linter.unusedVariables false in
theorem gs_sc4_accept :
    ∀ (n k_iter m_cur k_left : Int)
      (mate wmate nxt : Int → Int)
      (pref rank : Int → Int → Int)
      (m_cur' k_left' : Int)
      (mate' wmate' nxt' : Int → Int),
    (n ≥ 1 ∧ k_iter ≥ 0 ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → mate mm = -1) ∧
     (∀ (ww : Int), (0 ≤ ww ∧ ww < n) → wmate ww = -1) ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → nxt mm = 0) ∧
     (∀ (mm jj : Int), (0 ≤ mm ∧ mm < n ∧ 0 ≤ jj ∧ jj < n) →
        0 ≤ pref mm jj ∧ pref mm jj < n) ∧
     (∀ (ww mm : Int), (0 ≤ ww ∧ ww < n ∧ 0 ≤ mm ∧ mm < n) →
        0 ≤ rank ww mm ∧ rank ww mm < n)) →
    0 ≤ k_left → k_left ≤ k_iter → n ≥ 1 →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate mm = GSMate pref rank n (k_iter - k_left) mm) →
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate ww = GSWMate pref rank n (k_iter - k_left) ww) →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt mm = GSNxt pref rank n (k_iter - k_left) mm) →
    0 ≤ m_cur → m_cur < n →
    (k_left > 0 ∧ mate m_cur = -1 ∧ nxt m_cur < n ∧
     (wmate (pref m_cur (nxt m_cur)) = -1 ∨
      rank (pref m_cur (nxt m_cur)) m_cur <
      rank (pref m_cur (nxt m_cur)) (wmate (pref m_cur (nxt m_cur))))) →
    mate' = store (store mate (wmate (pref m_cur (nxt m_cur))) (-1)) m_cur (pref m_cur (nxt m_cur)) →
    wmate' = store wmate (pref m_cur (nxt m_cur)) m_cur →
    nxt' = store nxt m_cur (nxt m_cur + 1) →
    m_cur' = ((m_cur + 1) - ((m_cur + 1) / n) * n) →
    k_left' = k_left - 1 →
    (0 ≤ k_left') ∧ (k_left' ≤ k_iter) ∧ (n ≥ 1) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate' mm = GSMate pref rank n (k_iter - k_left') mm) ∧
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate' ww = GSWMate pref rank n (k_iter - k_left') ww) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt' mm = GSNxt pref rank n (k_iter - k_left') mm) ∧
    (0 ≤ m_cur') ∧ (m_cur' < n) := by
  intros n k_iter m_cur k_left mate wmate nxt pref rank m_cur' k_left'
         mate' wmate' nxt' h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4
         h_tau_5 h_tau_6 h_tau_7 h_guard
         h_trans_mate h_trans_wmate h_trans_nxt h_trans_m_cur h_trans_k_left
  obtain ⟨h_g_loop, h_g_mate, h_g_nxt, h_g_wcond⟩ := h_guard
  have h_kk_ge : k_iter - k_left ≥ 0 := by omega
  have h_arg : k_iter - k_left' = (k_iter - k_left) + 1 := by omega
  -- Bridge tau-atoms to UF values.
  have h_mate_uf : GSMate pref rank n (k_iter - k_left) m_cur = -1 := by
    have := h_tau_3 m_cur ⟨h_tau_6, h_tau_7⟩; omega
  have h_nxt_eq : GSNxt pref rank n (k_iter - k_left) m_cur = nxt m_cur := by
    have := h_tau_5 m_cur ⟨h_tau_6, h_tau_7⟩; omega
  have h_nxt_uf : GSNxt pref rank n (k_iter - k_left) m_cur < n := by
    rw [h_nxt_eq]; exact h_g_nxt
  -- The woman = pref m_cur (nxt m_cur) = pref m_cur (GSNxt(kk)[m_cur]).
  set w := pref m_cur (nxt m_cur) with h_w_def
  have h_w_eq : pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur) = w := by
    rw [h_nxt_eq]
  -- w bounds.
  obtain ⟨_, _, _, _, _, h_pref_range, _⟩ := h_pre
  have h_nxt_ge0 : 0 ≤ nxt m_cur := by
    rw [← h_nxt_eq]
    exact gs_nxt_nonneg pref rank n (k_iter - k_left) m_cur
            ⟨h_kk_ge, h_tau_6, h_tau_7⟩
  have h_w_bounds : 0 ≤ w ∧ w < n :=
    h_pref_range m_cur (nxt m_cur) ⟨h_tau_6, h_tau_7, h_nxt_ge0, h_g_nxt⟩
  have h_wcond_uf :
      GSWMate pref rank n (k_iter - k_left)
        (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) = -1 ∨
      rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) m_cur <
      rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur))
        (GSWMate pref rank n (k_iter - k_left)
          (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur))) := by
    rw [h_w_eq]
    have h_wmate_alg := h_tau_4 w h_w_bounds
    cases h_g_wcond with
    | inl h => left; rw [← h_wmate_alg]; exact h
    | inr h => right; rw [← h_wmate_alg]; exact h
  -- Apply ACCEPT axioms.
  have h_accept_pre :
      k_iter - k_left ≥ 0 ∧ 0 ≤ m_cur ∧ m_cur < n ∧
      GSMate pref rank n (k_iter - k_left) m_cur = -1 ∧
      GSNxt pref rank n (k_iter - k_left) m_cur < n ∧
      (GSWMate pref rank n (k_iter - k_left)
         (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) = -1 ∨
       rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) m_cur <
       rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur))
         (GSWMate pref rank n (k_iter - k_left)
           (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)))) :=
    ⟨h_kk_ge, h_tau_6, h_tau_7, h_mate_uf, h_nxt_uf, h_wcond_uf⟩
  have h_at_mm := gs_accept_mate_at_mm pref rank n (k_iter - k_left) m_cur h_accept_pre
  have h_at_w  := gs_accept_wmate_at_w pref rank n (k_iter - k_left) m_cur h_accept_pre
  have h_at_nx := gs_accept_nxt_at_mm  pref rank n (k_iter - k_left) m_cur h_accept_pre
  have h_other_m := gs_accept_mate_other pref rank n (k_iter - k_left) m_cur h_accept_pre
  have h_other_w := gs_accept_wmate_other pref rank n (k_iter - k_left) m_cur h_accept_pre
  have h_other_nx := gs_accept_nxt_other pref rank n (k_iter - k_left) m_cur h_accept_pre
  -- wmate[w_alg] in UF world.
  have h_wmate_uf : GSWMate pref rank n (k_iter - k_left) w = wmate w := by
    rw [h_tau_4 w h_w_bounds]
  -- Now subst the transitions and refine.
  subst h_trans_mate h_trans_wmate h_trans_nxt h_trans_m_cur h_trans_k_left
  refine ⟨?_, ?_, h_tau_2, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  -- mate' conjunct.
  · intro mm hmm
    rw [h_arg]
    by_cases h_mm_eq : mm = m_cur
    · -- mm = m_cur: outer store fires → w.
      rw [h_mm_eq]
      simp [store]
      rw [h_at_mm]
      exact h_w_eq.symm
    · -- mm ≠ m_cur.
      by_cases h_mm_w : mm = wmate w
      · -- mm = wmate w.  Two sub-cases: wmate w = -1 (then mm = -1, but mm ≥ 0) or wmate w ≠ -1.
        by_cases h_wmate_free : wmate w = -1
        · -- wmate w = -1 means mm = -1, but hmm says mm ≥ 0.  Contradiction.
          exfalso; obtain ⟨hl, _⟩ := hmm
          rw [h_mm_w, h_wmate_free] at hl
          omega
        · -- wmate w ≠ -1: displacement.  mate' mm = -1, GSMate(kk+1)[mm] = -1.
          rw [h_mm_w]
          have h_wmate_ne_m_cur : wmate w ≠ m_cur := by
            intro h_contra
            apply h_mm_eq
            rw [h_mm_w, h_contra]
          simp [store, h_wmate_ne_m_cur]
          -- Now goal: -1 = GSMate(kk+1)[wmate w].
          have h_displaced : GSMate pref rank n (k_iter - k_left + 1)
              (GSWMate pref rank n (k_iter - k_left) (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur))) = -1 := by
            apply gs_accept_mate_displaced pref rank n (k_iter - k_left) m_cur
            refine ⟨h_kk_ge, h_tau_6, h_tau_7, h_mate_uf, h_nxt_uf, ?_, ?_⟩
            · rw [h_w_eq, h_wmate_uf]; exact h_wmate_free
            · -- Need rank-strict inequality from h_g_wcond.
              cases h_g_wcond with
              | inl h => exfalso; exact h_wmate_free h
              | inr h =>
                rw [h_w_eq, h_wmate_uf]
                exact h
          rw [h_w_eq, h_wmate_uf] at h_displaced
          exact h_displaced.symm
      · -- mm ≠ m_cur AND mm ≠ wmate w.  Both stores skip.
        simp [store, h_mm_eq, h_mm_w]
        -- Goal: mate mm = GSMate(kk+1)[mm].
        -- Use h_other_m + h_tau_3.
        have h_other : GSMate pref rank n (k_iter - k_left + 1) mm =
                       GSMate pref rank n (k_iter - k_left) mm := by
          apply h_other_m
          refine ⟨hmm.1, hmm.2, h_mm_eq, ?_⟩
          rw [h_w_eq, h_wmate_uf]
          exact h_mm_w
        rw [h_other]
        exact h_tau_3 mm hmm
  -- wmate' conjunct.
  · intro ww hww
    rw [h_arg]
    by_cases h_ww_eq : ww = w
    · rw [h_ww_eq]
      simp [store]
      have := h_at_w
      rw [h_w_eq] at this
      exact this.symm
    · simp [store, h_ww_eq]
      have h_other : GSWMate pref rank n (k_iter - k_left + 1) ww =
                     GSWMate pref rank n (k_iter - k_left) ww := by
        apply h_other_w
        refine ⟨hww.1, hww.2, ?_⟩
        rw [h_w_eq]; exact h_ww_eq
      rw [h_other]
      exact h_tau_4 ww hww
  -- nxt' conjunct.
  · intro mm hmm
    rw [h_arg]
    by_cases h_mm_eq : mm = m_cur
    · rw [h_mm_eq]
      simp [store]
      have := h_at_nx
      omega
    · simp [store, h_mm_eq]
      have h_other : GSNxt pref rank n (k_iter - k_left + 1) mm =
                     GSNxt pref rank n (k_iter - k_left) mm :=
        h_other_nx mm ⟨hmm.1, hmm.2, h_mm_eq⟩
      rw [h_other]
      exact h_tau_5 mm hmm
  · exact (mod_subtraction_bounds (m_cur + 1) n h_tau_2 (by omega)).1
  · exact (mod_subtraction_bounds (m_cur + 1) n h_tau_2 (by omega)).2

-- ─── sc6: safety branch=2 (REJECT) ──────────────────────────
set_option linter.unusedVariables false in
theorem gs_sc6_reject :
    ∀ (n k_iter m_cur k_left : Int)
      (mate wmate nxt : Int → Int)
      (pref rank : Int → Int → Int)
      (m_cur' k_left' : Int)
      (nxt' : Int → Int),
    (n ≥ 1 ∧ k_iter ≥ 0 ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → mate mm = -1) ∧
     (∀ (ww : Int), (0 ≤ ww ∧ ww < n) → wmate ww = -1) ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → nxt mm = 0) ∧
     (∀ (mm jj : Int), (0 ≤ mm ∧ mm < n ∧ 0 ≤ jj ∧ jj < n) →
        0 ≤ pref mm jj ∧ pref mm jj < n) ∧
     (∀ (ww mm : Int), (0 ≤ ww ∧ ww < n ∧ 0 ≤ mm ∧ mm < n) →
        0 ≤ rank ww mm ∧ rank ww mm < n)) →
    0 ≤ k_left → k_left ≤ k_iter → n ≥ 1 →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate mm = GSMate pref rank n (k_iter - k_left) mm) →
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate ww = GSWMate pref rank n (k_iter - k_left) ww) →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt mm = GSNxt pref rank n (k_iter - k_left) mm) →
    0 ≤ m_cur → m_cur < n →
    (k_left > 0 ∧ mate m_cur = -1 ∧ nxt m_cur < n ∧
     ¬ (wmate (pref m_cur (nxt m_cur)) = -1 ∨
        rank (pref m_cur (nxt m_cur)) m_cur <
        rank (pref m_cur (nxt m_cur)) (wmate (pref m_cur (nxt m_cur))))) →
    nxt' = store nxt m_cur (nxt m_cur + 1) →
    m_cur' = ((m_cur + 1) - ((m_cur + 1) / n) * n) →
    k_left' = k_left - 1 →
    (0 ≤ k_left') ∧ (k_left' ≤ k_iter) ∧ (n ≥ 1) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate mm = GSMate pref rank n (k_iter - k_left') mm) ∧
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate ww = GSWMate pref rank n (k_iter - k_left') ww) ∧
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt' mm = GSNxt pref rank n (k_iter - k_left') mm) ∧
    (0 ≤ m_cur') ∧ (m_cur' < n) := by
  intros n k_iter m_cur k_left mate wmate nxt pref rank m_cur' k_left' nxt'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5
         h_tau_6 h_tau_7 h_guard h_trans_nxt h_trans_m_cur h_trans_k_left
  obtain ⟨h_g_loop, h_g_mate, h_g_nxt, h_g_wcond_neg⟩ := h_guard
  have h_kk_ge : k_iter - k_left ≥ 0 := by omega
  have h_arg : k_iter - k_left' = (k_iter - k_left) + 1 := by omega
  have h_mate_uf : GSMate pref rank n (k_iter - k_left) m_cur = -1 := by
    have := h_tau_3 m_cur ⟨h_tau_6, h_tau_7⟩; omega
  have h_nxt_eq : GSNxt pref rank n (k_iter - k_left) m_cur = nxt m_cur := by
    have := h_tau_5 m_cur ⟨h_tau_6, h_tau_7⟩; omega
  have h_nxt_uf : GSNxt pref rank n (k_iter - k_left) m_cur < n := by
    rw [h_nxt_eq]; exact h_g_nxt
  set w := pref m_cur (nxt m_cur) with h_w_def
  have h_w_eq : pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur) = w := by
    rw [h_nxt_eq]
  obtain ⟨_, _, _, _, _, h_pref_range, _⟩ := h_pre
  have h_nxt_ge0 : 0 ≤ nxt m_cur := by
    rw [← h_nxt_eq]
    exact gs_nxt_nonneg pref rank n (k_iter - k_left) m_cur
            ⟨h_kk_ge, h_tau_6, h_tau_7⟩
  have h_w_bounds : 0 ≤ w ∧ w < n :=
    h_pref_range m_cur (nxt m_cur) ⟨h_tau_6, h_tau_7, h_nxt_ge0, h_g_nxt⟩
  have h_wmate_uf : GSWMate pref rank n (k_iter - k_left) w = wmate w := by
    rw [h_tau_4 w h_w_bounds]
  -- Lift the REJECT negation to UF world.
  have h_wcond_neg_uf :
      ¬ (GSWMate pref rank n (k_iter - k_left)
           (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) = -1 ∨
         rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) m_cur <
         rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur))
           (GSWMate pref rank n (k_iter - k_left)
             (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)))) := by
    rw [h_w_eq, h_wmate_uf]
    exact h_g_wcond_neg
  have h_reject_pre :
      k_iter - k_left ≥ 0 ∧ 0 ≤ m_cur ∧ m_cur < n ∧
      GSMate pref rank n (k_iter - k_left) m_cur = -1 ∧
      GSNxt pref rank n (k_iter - k_left) m_cur < n ∧
      ¬ (GSWMate pref rank n (k_iter - k_left)
           (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) = -1 ∨
         rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)) m_cur <
         rank (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur))
           (GSWMate pref rank n (k_iter - k_left)
             (pref m_cur (GSNxt pref rank n (k_iter - k_left) m_cur)))) :=
    ⟨h_kk_ge, h_tau_6, h_tau_7, h_mate_uf, h_nxt_uf, h_wcond_neg_uf⟩
  have h_r_nx := gs_reject_nxt_at_mm pref rank n (k_iter - k_left) m_cur h_reject_pre
  have h_r_m  := gs_reject_mate_all  pref rank n (k_iter - k_left) m_cur h_reject_pre
  have h_r_w  := gs_reject_wmate_all pref rank n (k_iter - k_left) m_cur h_reject_pre
  have h_r_nx_other := gs_reject_nxt_other pref rank n (k_iter - k_left) m_cur h_reject_pre
  subst h_trans_nxt h_trans_m_cur h_trans_k_left
  refine ⟨?_, ?_, h_tau_2, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  -- mate' = mate (preserved) conjunct.
  · intro mm hmm
    rw [h_arg]
    rw [h_r_m mm hmm]
    exact h_tau_3 mm hmm
  -- wmate' = wmate (preserved) conjunct.
  · intro ww hww
    rw [h_arg]
    rw [h_r_w ww hww]
    exact h_tau_4 ww hww
  -- nxt' conjunct.
  · intro mm hmm
    rw [h_arg]
    by_cases h_mm_eq : mm = m_cur
    · rw [h_mm_eq]
      simp [store]
      omega
    · simp [store, h_mm_eq]
      rw [h_r_nx_other mm ⟨hmm.1, hmm.2, h_mm_eq⟩]
      exact h_tau_5 mm hmm
  · exact (mod_subtraction_bounds (m_cur + 1) n h_tau_2 (by omega)).1
  · exact (mod_subtraction_bounds (m_cur + 1) n h_tau_2 (by omega)).2

-- ─── sc9: L0 final bundle ⇒ post ────────────────────────────
--
-- sc9 closes the loop: at termination (¬ (k_left' > 0)) plus
-- the invariant `k_left' ≥ 0` from τ pins k_left' = 0, so the
-- recursive-UF equality at iter (k_iter - k_left') = k_iter
-- matches the bench's post directly.
--
-- Signature follows the FLAT chain-bundle translator: pre-state
-- binders + primed binders for loop-modified vars, h_tau at the
-- primed (loop-exit) state.
set_option linter.unusedVariables false in
theorem gs_sc9_final :
    ∀ (n k_iter m_cur k_left : Int)
      (mate wmate nxt : Int → Int)
      (pref rank : Int → Int → Int)
      (m_cur' k_left' : Int)
      (mate' wmate' nxt' : Int → Int),
    (n ≥ 1 ∧ k_iter ≥ 0 ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → mate mm = -1) ∧
     (∀ (ww : Int), (0 ≤ ww ∧ ww < n) → wmate ww = -1) ∧
     (∀ (mm : Int), (0 ≤ mm ∧ mm < n) → nxt mm = 0) ∧
     (∀ (mm jj : Int), (0 ≤ mm ∧ mm < n ∧ 0 ≤ jj ∧ jj < n) →
        0 ≤ pref mm jj ∧ pref mm jj < n) ∧
     (∀ (ww mm : Int), (0 ≤ ww ∧ ww < n ∧ 0 ≤ mm ∧ mm < n) →
        0 ≤ rank ww mm ∧ rank ww mm < n)) →
    0 ≤ k_left' → k_left' ≤ k_iter → n ≥ 1 →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate' mm = GSMate pref rank n (k_iter - k_left') mm) →
    (∀ (ww : Int), (0 ≤ ww ∧ ww < n) →
       wmate' ww = GSWMate pref rank n (k_iter - k_left') ww) →
    (∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       nxt' mm = GSNxt pref rank n (k_iter - k_left') mm) →
    0 ≤ m_cur' → m_cur' < n →
    ¬ (k_left' > 0) →
    ∀ (mm : Int), (0 ≤ mm ∧ mm < n) →
       mate' mm = GSMate pref rank n k_iter mm := by
  intros n k_iter m_cur k_left mate wmate nxt pref rank m_cur' k_left'
         mate' wmate' nxt' h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4
         h_tau_5 h_tau_6 h_tau_7 h_not_g mm hmm
  have h_keq : k_left' = 0 := by omega
  have := h_tau_3 mm hmm
  rw [h_keq] at this
  simpa using this

end SynthLean.Y2Corpus.GaleShapley
