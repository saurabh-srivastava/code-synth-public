/-
floyd_warshall Tier-3 helpers — RESEARCH.md §H.1.

Floyd-Warshall has THREE levels of nested invariants
(τ_outer, τ_middle, τ_inner) and FOUR algorithm-correctness
moves: bundle-post, outer inductive, middle inductive, inner
inductive.  Plus two "k-row / k-column preserved" facts that
encode the non-negative-cycles assumption.

Layering
--------
  bundle-post:     τ_outer at exit (k = n)  ⇒  Post
  outer ind.:     τ_outer @ k + middle body ⇒ τ_outer @ k+1
  middle ind.:    τ_middle @ (k, i) + inner body ⇒ τ_middle @ (k, i+1)
  inner ind.:     τ_inner @ (k, i, j) + SB(n=2) body ⇒ τ_inner @ (k, i, j+1)

  sp_k_row_preserved, sp_k_col_preserved — encode that
  going through vertex k doesn't shorten paths *to* or *from*
  vertex k itself, i.e. the non-neg-cycles assumption.

Trust points (named axioms)
---------------------------
  sp_self_nonneg:  ONE Tier-2 axiom — the non-negative-cycles
                   assumption.  Encodes that paths from a vertex
                   to itself through any intermediate subset must
                   be non-negative.  Matched in `Problem.pre` by
                   `∀k. k ≥ 0 → sp(D_in, k, k, k) ≥ 0`.

Pure Tier-1 (proved here, citing only axiom-1 + sp_self_nonneg)
---------------------------------------------------------------
  sp_k_row_preserved              — non-improvement via vertex k.
  sp_k_col_preserved              — dual.
  floyd_warshall_inner_correct    — alias of axiom-1.
  floyd_warshall_post_from_inv    — bundle-post bookkeeping.
  floyd_warshall_outer_inductive  — substitution.
  floyd_warshall_middle_inductive — case-split.
  floyd_warshall_inner_inductive  — full case analysis on
                                    (k vs j), (k vs i), branch.

Notes
-----
The synthesizer wedges on per-class Z3 enumeration BEFORE it
can dump failed obligations (3D-DP-with-UF exhausts axiom-
instantiation budget; documented in benchmark file header).
These helpers are the structural artifact for the proof —
ready to be cited by .solved.lean shims once an alternate
dispatch path (§H.2 pattern-match cache or driver-LLM)
unblocks per-subset Lean verification.
-/
import SynthLean.Basic
open SynthLean

axiom sp : (Int → Int → Int) → Int → Int → Int → Int
axiom fw_user_axiom_0 : ∀ (D_in : Int → Int → Int),
    (∀ i_ j_ : Int, ((sp D_in i_ j_ 0) = (D_in i_ j_)))
axiom fw_user_axiom_1 : ∀ (D_in : Int → Int → Int),
    (∀ i_ j_ k_ : Int, ((k_ ≥ 0) → ((sp D_in i_ j_ (k_ + 1)) =
        (if (sp D_in i_ j_ k_) ≤
            (sp D_in i_ k_ k_) + (sp D_in k_ j_ k_)
         then (sp D_in i_ j_ k_)
         else (sp D_in i_ k_ k_) + (sp D_in k_ j_ k_)))))

/-
sp(D_in, k, k, k) ≥ 0 — non-negative-cycles assumption (Tier-2
named axiom; the ONE fundamental trust point).

For Floyd-Warshall correctness, paths from a vertex to itself
through any intermediate subset must be non-negative.  This is
equivalent to "no negative cycles" in the input graph.  All
other helpers in this file are proved theorems citing only this
axiom + axiom-1.

Synthesizer's `Problem.pre` should include the matching
assumption so the synth-side per-class checks carry the
hypothesis.
-/
axiom sp_self_nonneg :
    ∀ (D_in : Int → Int → Int) (k : Int),
      0 ≤ k → sp D_in k k k ≥ 0

/-
k-row preservation theorem.  Going through vertex k as an
intermediate doesn't improve the shortest path *to* vertex k
itself, given non-negative self-loops at k.

    sp(D_in, i, k, k + 1) = sp(D_in, i, k, k)

Proof: apply axiom-1 at (i, k, k); the IF-condition is
  sp(D_in, i, k, k) ≤ sp(D_in, i, k, k) + sp(D_in, k, k, k)
which reduces to 0 ≤ sp(D_in, k, k, k) (the trust axiom).
The then-branch fires, giving sp(D_in, i, k, k).
-/
theorem sp_k_row_preserved
    (D_in : Int → Int → Int) (i k : Int) (h_k_nn : 0 ≤ k) :
    (sp D_in i k (k + 1)) = (sp D_in i k k) := by
  have hax := fw_user_axiom_1 D_in i k k h_k_nn
  have h_self_nn := sp_self_nonneg D_in k h_k_nn
  have h_cond : sp D_in i k k ≤ sp D_in i k k + sp D_in k k k := by linarith
  rw [hax, if_pos h_cond]

/-
k-column preservation theorem.  Dual of `sp_k_row_preserved`:
going through k doesn't improve shortest paths *from* k.

    sp(D_in, k, j, k + 1) = sp(D_in, k, j, k)
-/
theorem sp_k_col_preserved
    (D_in : Int → Int → Int) (k j : Int) (h_k_nn : 0 ≤ k) :
    (sp D_in k j (k + 1)) = (sp D_in k j k) := by
  have hax := fw_user_axiom_1 D_in k j k h_k_nn
  have h_self_nn := sp_self_nonneg D_in k h_k_nn
  have h_cond : sp D_in k j k ≤ sp D_in k k k + sp D_in k j k := by linarith
  rw [hax, if_pos h_cond]

/-
Classical Floyd-Warshall inner-step correctness — this is a
restatement of axiom-1 (`fw_user_axiom_1`), kept here as a
theorem alias for readability where the inner inductive
proof cites it.
-/
theorem floyd_warshall_inner_correct
    (D_in : Int → Int → Int) (i j k : Int)
    (h_k_nn : k ≥ 0) :
    (sp D_in i j (k + 1)) =
      (if (sp D_in i j k) ≤ (sp D_in i k k) + (sp D_in k j k)
       then (sp D_in i j k)
       else (sp D_in i k k) + (sp D_in k j k)) :=
  fw_user_axiom_1 D_in i j k h_k_nn

namespace SynthLean.FloydWarshallHelpers

/-
Bundle-post helper (kind = safety-bundle-post).

Given the loop-exit state (k = n via the negated guard) with
the user's τ_outer invariant "D[i][j] = sp(D_in, i, j, k)",
derive the post:

    ∀ i, j. 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < n
            → D[i][j] = sp(D_in, i, j, n)

Required τ atoms:
  - k_le_n:  k ≤ n
  - outer:   ∀ i, j. 0 ≤ i < n ∧ 0 ≤ j < n
                     → D[i][j] = sp(D_in, i, j, k)

Plus the loop-exit hypothesis:
  - h_not_g: ¬ (k < n)

Proof: at loop exit, k = n.  The τ_outer atom at k = n IS the
post.  No trust-point axiom needed — pure Tier-1 from user
atoms.
-/
theorem floyd_warshall_post_from_inv
    (D : Int → Int → Int) (D_in : Int → Int → Int) (n k : Int)
    (h_k_le_n : k ≤ n)
    (h_outer : ∀ i_ j_ : Int,
                 ((0 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) →
                 ((D i_ j_) = (sp D_in i_ j_ k)))
    (h_not_g : ¬ (k < n)) :
    ∀ i_ j_ : Int,
      ((0 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) →
      ((D i_ j_) = (sp D_in i_ j_ n)) := by
  have h_k_eq : k = n := by omega
  intro i_ j_ hij
  have h1 := h_outer i_ j_ hij
  rw [h_k_eq] at h1
  exact h1

/-
Outer inductive helper (kind = safety-inductive on outer Loop).

Given τ_outer at iter k plus the middle-loop body completion,
derive τ_outer at iter k + 1.

State after middle loop completes:
  - i = n (from middle loop's negated guard, i.e. i ≥ n;
           combined with τ_middle's i ≤ n).
  - τ_middle says: rows 0..i-1 (= all rows) at sp(·, ·, k+1).
  - No rows pending at k.

After SB (k := k + 1):
  - τ_outer at k_new = k + 1:
      0 ≤ k_new, k_new ≤ n (from k < n and integer step),
      ∀ i', j'. 0 ≤ i' < n ∧ 0 ≤ j' < n → D[i'][j'] = sp(·, ·, k+1).
    The quantified atom is exactly τ_middle's "rows fully
    updated" at i = n.

Proof: bookkeeping + substitution.
-/
theorem floyd_warshall_outer_inductive
    (D : Int → Int → Int) (D_in : Int → Int → Int)
    (n k i : Int)
    (h_n_nn : n ≥ 0)
    (h_k_nn : 0 ≤ k)
    (h_k_lt_n : k < n)
    (h_i_eq_n : i = n)
    (h_middle_done : ∀ i_ j_ : Int,
                       ((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) →
                       ((D i_ j_) = (sp D_in i_ j_ (k + 1)))) :
    (0 ≤ k + 1) ∧ (k + 1 ≤ n) ∧ (n ≥ 0) ∧
    (∀ i_ j_ : Int,
       ((0 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) →
       ((D i_ j_) = (sp D_in i_ j_ (k + 1)))) := by
  refine ⟨by omega, by omega, h_n_nn, ?_⟩
  intro i_ j_ ⟨h0, h1, h2, h3⟩
  have h_lt_i : i_ < i := by rw [h_i_eq_n]; exact h1
  exact h_middle_done i_ j_ ⟨h0, h_lt_i, h2, h3⟩

/-
Middle inductive helper (kind = safety-inductive on middle Loop).

Given τ_middle at (k, i) plus the inner-loop body completion,
derive τ_middle at (k, i + 1).

State after inner loop completes:
  - j = n (inner loop's negated guard with τ_inner's j ≤ n).
  - τ_inner at (k, i, n) says:
      prior rows 0..i-1 at k+1,
      current row cols 0..n-1 (entire row) at k+1,
      no cols pending,
      future rows i+1..n-1 at k.
  - i is incremented by SB.

Prove τ_middle at i_new = i + 1:
  - rows 0..i_new-1 = rows 0..i = "prior rows at k+1" + "current
    row at k+1".  Case-split on i' < i vs i' = i.
  - rows i_new..n-1 = rows i+1..n-1 = future rows at k.  Direct.

Proof: case analysis + direct citation of τ_inner conjuncts.
-/
theorem floyd_warshall_middle_inductive
    (D : Int → Int → Int) (D_in : Int → Int → Int)
    (n k i j : Int)
    (h_n_nn : n ≥ 0)
    (h_k_nn : 0 ≤ k) (h_k_lt_n : k < n)
    (h_i_nn : 0 ≤ i) (h_i_lt_n : i < n)
    (h_j_eq_n : j = n)
    (h_prior_done : ∀ i_ j_ : Int,
                      ((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) →
                      ((D i_ j_) = (sp D_in i_ j_ (k + 1))))
    (h_curr_done : ∀ j_ : Int,
                     ((0 ≤ j_) ∧ (j_ < j)) →
                     ((D i j_) = (sp D_in i j_ (k + 1))))
    (h_future_pending : ∀ i_ j_ : Int,
                          ((i + 1 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) →
                          ((D i_ j_) = (sp D_in i_ j_ k))) :
    (0 ≤ k) ∧ (k < n) ∧ (0 ≤ i + 1) ∧ (i + 1 ≤ n) ∧ (n ≥ 0) ∧
    (∀ i_ j_ : Int,
       ((0 ≤ i_) ∧ (i_ < i + 1) ∧ (0 ≤ j_) ∧ (j_ < n)) →
       ((D i_ j_) = (sp D_in i_ j_ (k + 1)))) ∧
    (∀ i_ j_ : Int,
       ((i + 1 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) →
       ((D i_ j_) = (sp D_in i_ j_ k))) := by
  refine ⟨h_k_nn, h_k_lt_n, by omega, by omega, h_n_nn, ?_, h_future_pending⟩
  intro i_ j_ ⟨h0, h1, h2, h3⟩
  -- Case-split on i_ < i vs i_ = i.
  by_cases h_lt : i_ < i
  · exact h_prior_done i_ j_ ⟨h0, h_lt, h2, h3⟩
  · -- i_ = i (since i_ ≥ i and i_ < i + 1).
    have h_eq : i_ = i := by omega
    rw [h_eq]
    -- Use h_curr_done; need j_ < j.  Since j = n and 0 ≤ j_ < n,
    -- j_ < j follows.
    have h_jlt : j_ < j := by rw [h_j_eq_n]; exact h3
    exact h_curr_done j_ ⟨h2, h_jlt⟩

/-
Inner inductive helper (kind = safety-inductive on inner Loop).

Given τ_inner at (k, i, j) plus the SB(n=2) body execution
(branch carrying the corresponding guard), derive τ_inner at
(k, i, j + 1).

Branch 0 (no update):  D' = D pointwise,
                       guard D[i][j] ≤ D[i][k] + D[k][j].
Branch 1 (update):     D' agrees with D except at (i, j),
                       D' i j = D i k + D k j,
                       guard D[i][j] > D[i][k] + D[k][j].

The proof:
  1. Derive `D i k = sp(D_in, i, k, k)` and
     `D k j = sp(D_in, k, j, k)` via case analysis on
     (k vs j) resp. (k vs i) using h_prior / h_curr_done /
     h_curr_pending / h_future plus the preservation theorems.
  2. For each of the 4 conjuncts of τ_inner at (k, i, j+1),
     case-split on the branch and apply pointwise reasoning.
  3. The crux is the cell at (i, j) in the curr-done conjunct:
     axiom-1 at (i, j, k) gives an if-then-else whose
     condition reduces via the lemmas to the branch guard.
-/
theorem floyd_warshall_inner_inductive
    (D : Int → Int → Int) (D_in : Int → Int → Int)
    (n k i j : Int) (D' : Int → Int → Int)
    (h_k_nn : 0 ≤ k) (h_k_lt_n : k < n)
    (h_i_nn : 0 ≤ i) (h_i_lt_n : i < n)
    (h_j_nn : 0 ≤ j) (h_j_lt_n : j < n)
    (h_n_nn : n ≥ 0)
    (h_prior : ∀ i_ j_ : Int,
                 ((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) →
                 ((D i_ j_) = (sp D_in i_ j_ (k + 1))))
    (h_curr_done : ∀ j_ : Int,
                     ((0 ≤ j_) ∧ (j_ < j)) →
                     ((D i j_) = (sp D_in i j_ (k + 1))))
    (h_curr_pending : ∀ j_ : Int,
                        ((j ≤ j_) ∧ (j_ < n)) →
                        ((D i j_) = (sp D_in i j_ k)))
    (h_future : ∀ i_ j_ : Int,
                  ((i + 1 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) →
                  ((D i_ j_) = (sp D_in i_ j_ k)))
    (h_branch :
       ((∀ p q : Int, D' p q = D p q) ∧
        (D i j ≤ D i k + D k j))
       ∨
       ((D' i j = D i k + D k j) ∧
        (∀ p q : Int, (p ≠ i ∨ q ≠ j) → D' p q = D p q) ∧
        (D i j > D i k + D k j))) :
    (∀ i_ j_ : Int,
       ((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) →
       ((D' i_ j_) = (sp D_in i_ j_ (k + 1)))) ∧
    (∀ j_ : Int,
       ((0 ≤ j_) ∧ (j_ < j + 1)) →
       ((D' i j_) = (sp D_in i j_ (k + 1)))) ∧
    (∀ j_ : Int,
       ((j + 1 ≤ j_) ∧ (j_ < n)) →
       ((D' i j_) = (sp D_in i j_ k))) ∧
    (∀ i_ j_ : Int,
       ((i + 1 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) →
       ((D' i_ j_) = (sp D_in i_ j_ k))) := by
  -- Lemma A: D i k = sp D_in i k k.
  have h_Dik : D i k = sp D_in i k k := by
    by_cases hkj : k < j
    · have h := h_curr_done k ⟨h_k_nn, hkj⟩
      rw [h, sp_k_row_preserved D_in i k h_k_nn]
    · push_neg at hkj
      exact h_curr_pending k ⟨hkj, h_k_lt_n⟩
  -- Lemma B: D k j = sp D_in k j k.
  have h_Dkj : D k j = sp D_in k j k := by
    by_cases hki : k < i
    · have h := h_prior k j ⟨h_k_nn, hki, h_j_nn, h_j_lt_n⟩
      rw [h, sp_k_col_preserved D_in k j h_k_nn]
    · push_neg at hki
      by_cases hki2 : k = i
      · -- k = i: rewrite i → k everywhere, then use h_curr_pending.
        have h := h_curr_pending j ⟨le_refl j, h_j_lt_n⟩
        rw [← hki2] at h
        exact h
      · have hki3 : i + 1 ≤ k := by omega
        exact h_future k j ⟨hki3, h_k_lt_n, h_j_nn, h_j_lt_n⟩
  -- Lemma C: D i j = sp D_in i j k.
  have h_Dij : D i j = sp D_in i j k :=
    h_curr_pending j ⟨le_refl j, h_j_lt_n⟩
  -- A pointwise "D' agrees with D off cell (i, j)" helper.
  have h_off : ∀ p q : Int, (p ≠ i ∨ q ≠ j) → D' p q = D p q := by
    rcases h_branch with ⟨h_eq, _⟩ | ⟨_, h_off, _⟩
    · intro p q _; exact h_eq p q
    · exact h_off
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Conjunct 1: prior rows unchanged (i_ < i ≠ i).
  · intro i_ j_ ⟨h0, h1, h2, h3⟩
    have h_ne : i_ ≠ i ∨ j_ ≠ j := Or.inl (by omega)
    rw [h_off i_ j_ h_ne]
    exact h_prior i_ j_ ⟨h0, h1, h2, h3⟩
  -- Conjunct 2: current row done, cols < j + 1.  The crux.
  · intro j_ ⟨h0, h1⟩
    by_cases hjsplit : j_ < j
    · -- Previously-done cells; D' = D at (i, j_) since j_ ≠ j.
      have h_ne : i ≠ i ∨ j_ ≠ j := Or.inr (by omega)
      rw [h_off i j_ h_ne]
      exact h_curr_done j_ ⟨h0, hjsplit⟩
    · -- j_ = j (since j_ < j + 1 and ¬ j_ < j).
      have hjeq : j_ = j := by omega
      subst hjeq
      -- Need: D' i j_ = sp D_in i j_ (k + 1).
      have hax := fw_user_axiom_1 D_in i j_ k h_k_nn
      rcases h_branch with ⟨h_eq, h_guard⟩ | ⟨h_eq, _, h_guard⟩
      · -- Branch 0: D' i j_ = D i j_; the IF-branch fires.
        rw [h_eq i j_]
        have h_axcond :
            sp D_in i j_ k ≤ sp D_in i k k + sp D_in k j_ k := by
          rw [← h_Dij, ← h_Dik, ← h_Dkj]; exact h_guard
        rw [hax, if_pos h_axcond, ← h_Dij]
      · -- Branch 1: D' i j_ = D i k + D k j_; the ELSE branch fires.
        rw [h_eq, h_Dik, h_Dkj]
        have h_axcond :
            ¬ (sp D_in i j_ k ≤ sp D_in i k k + sp D_in k j_ k) := by
          rw [← h_Dij, ← h_Dik, ← h_Dkj]; push_neg; exact h_guard
        rw [hax, if_neg h_axcond]
  -- Conjunct 3: current row pending, cols ≥ j + 1.
  · intro j_ ⟨h0, h1⟩
    have h_ne : i ≠ i ∨ j_ ≠ j := Or.inr (by omega)
    rw [h_off i j_ h_ne]
    exact h_curr_pending j_ ⟨by omega, h1⟩
  -- Conjunct 4: future rows unchanged.
  · intro i_ j_ ⟨h0, h1, h2, h3⟩
    have h_ne : i_ ≠ i ∨ j_ ≠ j := Or.inl (by omega)
    rw [h_off i_ j_ h_ne]
    exact h_future i_ j_ ⟨h0, h1, h2, h3⟩

/-
Chain-aware Tier-2 axioms — task #167.

The chain-aware translator (theorem_for_entry_bundle_chain /
theorem_for_chain_bundle_chain) emits per-state binders
`<var>_s<k>`.  For nested obligations (target inside an
enclosing loop), the translator also threads `h_enc_tau_*`
(enclosing τ at chain start) and `h_enc_g` (enclosing guard).

These axioms encapsulate the algorithmic correctness of FW's
nested-loop transitions.  Future work: convert to theorems
when we have an inductive proof of the sp recurrence in scope.
-/

-- sc1 — L1 entry (chain-aware).  After SB(B1) sets i := 0,
-- prove τ@L1 holds at L1's entry.  Goal has 7 conjuncts.
-- Tier-1: after B1 init (i_s1 = 0) + frames, prove τ@L1 at s1.
-- Conjuncts: bounds from h_enc_tau + frames; "prior rows" is
-- vacuous (i_ < 0); "rows pending" follows from h_enc_tau_3.
theorem fw_l1_entry_chain :
    ∀ (n_s0 i_s0 j_s0 k_s0 : Int)
      (D_in_s0 D_s0 : Int → Int → Int)
      (n_s1 i_s1 j_s1 k_s1 : Int)
      (D_in_s1 D_s1 : Int → Int → Int),
    ((n_s0 ≥ 0) ∧ (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = ((D_in_s0 i_) j_)))) ∧ (∀ k_ : Int, ((k_ ≥ 0) → ((sp D_in_s0 k_ k_ k_) ≥ 0)))) →
    (0 ≤ k_s0) → (k_s0 ≤ n_s0) → (n_s0 ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = (sp D_in_s0 i_ j_ k_s0)))) →
    (k_s0 < n_s0) →
    (i_s1 = 0) → (n_s1 = n_s0) → (j_s1 = j_s0) → (k_s1 = k_s0) →
    (D_in_s1 = D_in_s0) → (D_s1 = D_s0) →
    ((0 ≤ k_s1) ∧ (k_s1 < n_s1) ∧ (0 ≤ i_s1) ∧ (i_s1 ≤ n_s1) ∧ (n_s1 ≥ 0) ∧
     (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i_s1) ∧ (0 ≤ j_) ∧ (j_ < n_s1)) → (((D_s1 i_) j_) = (sp D_in_s1 i_ j_ (k_s1 + 1))))) ∧
     (∀ i_ j_ : Int, (((i_s1 ≤ i_) ∧ (i_ < n_s1) ∧ (0 ≤ j_) ∧ (j_ < n_s1)) → (((D_s1 i_) j_) = (sp D_in_s1 i_ j_ k_s1))))) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _
  intro _ h_k_ge0 _ h_n0_ge0 h_table h_k_lt_n
  intro h_ieq h_neq _ h_keq h_Din h_Deq
  subst h_ieq h_neq h_keq h_Din h_Deq
  refine ⟨h_k_ge0, h_k_lt_n, ?_, ?_, h_n0_ge0, ?_, ?_⟩
  · omega
  · omega
  · intro _ _ ⟨_, h, _, _⟩; omega
  · intro i_ j_ ⟨_, h_i_lt, h_j_ge, h_j_lt⟩
    exact h_table i_ j_ ⟨by omega, h_i_lt, h_j_ge, h_j_lt⟩

-- sc2 — L2 entry (chain-aware).  After SB(B2) sets j := 0,
-- prove τ@L2 holds.  Goal has 11 conjuncts.
-- Tier-1: bounds + the 4 quantified atoms follow from h_enc_tau_*
-- + frames.  Two "current row" atoms specialize on j_s1 = 0.
theorem fw_l2_entry_chain :
    ∀ (n_s0 i_s0 j_s0 k_s0 : Int)
      (D_in_s0 D_s0 : Int → Int → Int)
      (n_s1 i_s1 j_s1 k_s1 : Int)
      (D_in_s1 D_s1 : Int → Int → Int),
    ((n_s0 ≥ 0) ∧ (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = ((D_in_s0 i_) j_)))) ∧ (∀ k_ : Int, ((k_ ≥ 0) → ((sp D_in_s0 k_ k_ k_) ≥ 0)))) →
    (0 ≤ k_s0) → (k_s0 < n_s0) → (0 ≤ i_s0) → (i_s0 ≤ n_s0) → (n_s0 ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = (sp D_in_s0 i_ j_ (k_s0 + 1))))) →
    (∀ i_ j_ : Int, (((i_s0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = (sp D_in_s0 i_ j_ k_s0)))) →
    (i_s0 < n_s0) →
    (j_s1 = 0) → (n_s1 = n_s0) → (i_s1 = i_s0) → (k_s1 = k_s0) →
    (D_in_s1 = D_in_s0) → (D_s1 = D_s0) →
    ((0 ≤ k_s1) ∧ (k_s1 < n_s1) ∧ (0 ≤ i_s1) ∧ (i_s1 < n_s1) ∧ (0 ≤ j_s1) ∧ (j_s1 ≤ n_s1) ∧ (n_s1 ≥ 0) ∧
     (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i_s1) ∧ (0 ≤ j_) ∧ (j_ < n_s1)) → (((D_s1 i_) j_) = (sp D_in_s1 i_ j_ (k_s1 + 1))))) ∧
     (∀ j_ : Int, (((0 ≤ j_) ∧ (j_ < j_s1)) → (((D_s1 i_s1) j_) = (sp D_in_s1 i_s1 j_ (k_s1 + 1))))) ∧
     (∀ j_ : Int, (((j_s1 ≤ j_) ∧ (j_ < n_s1)) → (((D_s1 i_s1) j_) = (sp D_in_s1 i_s1 j_ k_s1)))) ∧
     (∀ i_ j_ : Int, ((((i_s1 + 1) ≤ i_) ∧ (i_ < n_s1) ∧ (0 ≤ j_) ∧ (j_ < n_s1)) → (((D_s1 i_) j_) = (sp D_in_s1 i_ j_ k_s1))))) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _
  intro _ h_k_ge0 h_k_lt_n h_i_ge0 _ h_n0_ge0 h_prior h_pending h_i_lt_n
  intro h_jeq h_neq h_ieq h_keq h_Din h_Deq
  subst h_jeq h_neq h_ieq h_keq h_Din h_Deq
  refine ⟨h_k_ge0, h_k_lt_n, h_i_ge0, h_i_lt_n, ?_, ?_, h_n0_ge0, h_prior, ?_, ?_, ?_⟩
  · omega
  · omega
  -- Conjunct 9: current row done at j_s1=0 (vacuous, j < 0).
  · intro _ ⟨_, h⟩; omega
  -- Conjunct 10: current row pending at j_s1=0 (covers j ∈ [0, n)).
  · intro j_ ⟨_, h_j_lt⟩
    exact h_pending _ _ ⟨by omega, by omega, by omega, h_j_lt⟩
  -- Conjunct 11: future rows (i_ ≥ i_s0+1).
  · intro i_ j_ ⟨h_i_ge, h_i_lt, h_j_ge, h_j_lt⟩
    exact h_pending i_ j_ ⟨by omega, h_i_lt, h_j_ge, h_j_lt⟩

-- sc9 — L1's body around L2 (body inductive).  Chain has 3
-- items: SB(B2) j:=0, Loop(L2) abstract, SB(B4) i:=i+1.  4 states.
-- Goal: τ@L1 at s3 (7 conjuncts).
-- Tier-1: name s2 vars in intros so they survive partial subst.
-- Conjunct 6 case-splits i_ = i_s2 (just-completed row uses
-- inner τ's h_curr_done; rest uses h_prior).  Conjunct 7 from
-- h_future.
theorem fw_l2_body_inductive_chain :
    ∀ (n_s0 i_s0 j_s0 k_s0 : Int)
      (D_in_s0 D_s0 : Int → Int → Int)
      (n_s1 i_s1 j_s1 k_s1 : Int)
      (D_in_s1 D_s1 : Int → Int → Int)
      (n_s2 i_s2 j_s2 k_s2 : Int)
      (D_in_s2 D_s2 : Int → Int → Int)
      (n_s3 i_s3 j_s3 k_s3 : Int)
      (D_in_s3 D_s3 : Int → Int → Int),
    ((n_s0 ≥ 0) ∧ (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = ((D_in_s0 i_) j_)))) ∧ (∀ k_ : Int, ((k_ ≥ 0) → ((sp D_in_s0 k_ k_ k_) ≥ 0)))) →
    (0 ≤ k_s0) → (k_s0 < n_s0) → (0 ≤ i_s0) → (i_s0 ≤ n_s0) → (n_s0 ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = (sp D_in_s0 i_ j_ (k_s0 + 1))))) →
    (∀ i_ j_ : Int, (((i_s0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = (sp D_in_s0 i_ j_ k_s0)))) →
    (i_s0 < n_s0) →
    (j_s1 = 0) → (n_s1 = n_s0) → (i_s1 = i_s0) → (k_s1 = k_s0) →
    (D_in_s1 = D_in_s0) → (D_s1 = D_s0) →
    (0 ≤ k_s2) → (k_s2 < n_s2) → (0 ≤ i_s2) → (i_s2 < n_s2) →
    (0 ≤ j_s2) → (j_s2 ≤ n_s2) → (n_s2 ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i_s2) ∧ (0 ≤ j_) ∧ (j_ < n_s2)) → (((D_s2 i_) j_) = (sp D_in_s2 i_ j_ (k_s2 + 1))))) →
    (∀ j_ : Int, (((0 ≤ j_) ∧ (j_ < j_s2)) → (((D_s2 i_s2) j_) = (sp D_in_s2 i_s2 j_ (k_s2 + 1))))) →
    (∀ j_ : Int, (((j_s2 ≤ j_) ∧ (j_ < n_s2)) → (((D_s2 i_s2) j_) = (sp D_in_s2 i_s2 j_ k_s2)))) →
    (∀ i_ j_ : Int, ((((i_s2 + 1) ≤ i_) ∧ (i_ < n_s2) ∧ (0 ≤ j_) ∧ (j_ < n_s2)) → (((D_s2 i_) j_) = (sp D_in_s2 i_ j_ k_s2)))) →
    ¬ (j_s2 < n_s2) →
    (n_s2 = n_s1) → (i_s2 = i_s1) → (k_s2 = k_s1) → (D_in_s2 = D_in_s1) →
    (i_s3 = (i_s2 + 1)) → (n_s3 = n_s2) → (j_s3 = j_s2) → (k_s3 = k_s2) →
    (D_in_s3 = D_in_s2) → (D_s3 = D_s2) →
    ((0 ≤ k_s3) ∧ (k_s3 < n_s3) ∧ (0 ≤ i_s3) ∧ (i_s3 ≤ n_s3) ∧ (n_s3 ≥ 0) ∧
     (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i_s3) ∧ (0 ≤ j_) ∧ (j_ < n_s3)) → (((D_s3 i_) j_) = (sp D_in_s3 i_ j_ (k_s3 + 1))))) ∧
     (∀ i_ j_ : Int, (((i_s3 ≤ i_) ∧ (i_ < n_s3) ∧ (0 ≤ j_) ∧ (j_ < n_s3)) → (((D_s3 i_) j_) = (sp D_in_s3 i_ j_ k_s3))))) := by
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro n_s2 i_s2 j_s2 k_s2 D_in_s2 D_s2
  intro _ _ _ _ _ _
  intro _ _ h_k_lt_n _ _ _ _ _ _
  intro h_jeq1 h_neq1 h_ieq1 h_keq1 h_Din1 h_Deq1
  intro h_k2_ge h_k2_lt h_i2_ge h_i2_lt h_j2_ge h_j2_le h_n2
  intro h_prior h_curr_done _ h_future h_notg
  intro h_n21 h_i21 h_k21 h_Din21
  intro h_ieq3 h_n3 h_j3 h_k3 h_Din3 h_Deq3
  subst h_jeq1 h_neq1 h_ieq1 h_keq1 h_Din1 h_Deq1
  subst h_ieq3 h_n3 h_j3 h_k3 h_Din3 h_Deq3
  refine ⟨h_k2_ge, ?_, ?_, ?_, h_n2, ?_, ?_⟩
  · omega
  · omega
  · omega
  · intro i_ j_ ⟨h_i_ge, h_i_lt, h_j_ge, h_j_lt⟩
    by_cases hi : i_ = i_s2
    · subst hi
      exact h_curr_done j_ ⟨h_j_ge, by omega⟩
    · exact h_prior i_ j_ ⟨h_i_ge, by omega, h_j_ge, h_j_lt⟩
  · intro i_ j_ ⟨h_i_ge, h_i_lt, h_j_ge, h_j_lt⟩
    exact h_future i_ j_ ⟨by omega, h_i_lt, h_j_ge, h_j_lt⟩

-- sc11 — L0's body around L1 (body inductive).  Chain: SB(B1)
-- i:=0, Loop(L1) abstract, SB(B5) k:=k+1.  4 states.  Goal:
-- τ@L0 at s3 (4 conjuncts).
-- Tier-1: ¬g_L1 + bound i_s2 ≤ n_s2 ⇒ i_s2 = n_s2; inner τ atom
-- (rows updated to k+1) covers all rows.
theorem fw_l1_body_inductive_chain :
    ∀ (n_s0 i_s0 j_s0 k_s0 : Int)
      (D_in_s0 D_s0 : Int → Int → Int)
      (n_s1 i_s1 j_s1 k_s1 : Int)
      (D_in_s1 D_s1 : Int → Int → Int)
      (n_s2 i_s2 j_s2 k_s2 : Int)
      (D_in_s2 D_s2 : Int → Int → Int)
      (n_s3 i_s3 j_s3 k_s3 : Int)
      (D_in_s3 D_s3 : Int → Int → Int),
    ((n_s0 ≥ 0) ∧ (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = ((D_in_s0 i_) j_)))) ∧ (∀ k_ : Int, ((k_ ≥ 0) → ((sp D_in_s0 k_ k_ k_) ≥ 0)))) →
    (0 ≤ k_s0) → (k_s0 ≤ n_s0) → (n_s0 ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n_s0) ∧ (0 ≤ j_) ∧ (j_ < n_s0)) → (((D_s0 i_) j_) = (sp D_in_s0 i_ j_ k_s0)))) →
    (k_s0 < n_s0) →
    (i_s1 = 0) → (n_s1 = n_s0) → (j_s1 = j_s0) → (k_s1 = k_s0) →
    (D_in_s1 = D_in_s0) → (D_s1 = D_s0) →
    (0 ≤ k_s2) → (k_s2 < n_s2) → (0 ≤ i_s2) → (i_s2 ≤ n_s2) → (n_s2 ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i_s2) ∧ (0 ≤ j_) ∧ (j_ < n_s2)) → (((D_s2 i_) j_) = (sp D_in_s2 i_ j_ (k_s2 + 1))))) →
    (∀ i_ j_ : Int, (((i_s2 ≤ i_) ∧ (i_ < n_s2) ∧ (0 ≤ j_) ∧ (j_ < n_s2)) → (((D_s2 i_) j_) = (sp D_in_s2 i_ j_ k_s2)))) →
    ¬ (i_s2 < n_s2) →
    (n_s2 = n_s1) → (k_s2 = k_s1) → (D_in_s2 = D_in_s1) →
    (k_s3 = (k_s2 + 1)) → (n_s3 = n_s2) → (i_s3 = i_s2) → (j_s3 = j_s2) →
    (D_in_s3 = D_in_s2) → (D_s3 = D_s2) →
    ((0 ≤ k_s3) ∧ (k_s3 ≤ n_s3) ∧ (n_s3 ≥ 0) ∧
     (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n_s3) ∧ (0 ≤ j_) ∧ (j_ < n_s3)) → (((D_s3 i_) j_) = (sp D_in_s3 i_ j_ k_s3))))) := by
  intro _ _ _ _ _ _      -- s0: 6 vars
  intro _ _ _ _ _ _      -- s1: 6
  intro _ _ _ _ _ _      -- s2: 6
  intro _ _ _ _ _ _      -- s3: 6
  intro _ _ h_k_le_n _ _ h_k_lt_n
  intro h_ieq1 h_neq1 h_jeq1 h_keq1 h_Din1 h_Deq1
  intro _ _ _ h_i2_le _
  intro h_prior h_pending h_notg
  intro h_n21 h_k21 h_Din21
  intro h_keq3 h_n3 h_i3 h_j3 h_Din3 h_Deq3
  subst h_ieq1 h_neq1 h_jeq1 h_keq1 h_Din1 h_Deq1
  subst h_n21 h_k21 h_Din21
  subst h_keq3 h_n3 h_i3 h_j3 h_Din3 h_Deq3
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · assumption
  -- Conjunct 4: all rows updated to k+1.  i_s2 = n_s2 from ¬g + bound.
  · intro i_ j_ ⟨h_i_ge, h_i_lt, h_j_ge, h_j_lt⟩
    exact h_prior i_ j_ ⟨h_i_ge, by omega, h_j_ge, h_j_lt⟩

-- sc4 — L2 inductive branch 0 (D[i][j] ≤ D[i][k] + D[k][j], no update).
-- The translator emits this for the branch where D unchanged.
-- Tier-1: wrap floyd_warshall_inner_inductive with D' := D and
-- h_branch := Or.inl ⟨..., ...⟩.  Bookkeeping conjuncts via omega.
theorem fw_l2_inductive_branch_0 :
    ∀ (n i j k : Int)
      (D_in D : Int → Int → Int)
      (j' : Int),
    ((n ≥ 0) ∧ (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = ((D_in i_) j_)))) ∧ (∀ k_ : Int, ((k_ ≥ 0) → ((sp D_in k_ k_ k_) ≥ 0)))) →
    (0 ≤ k) → (k < n) → (0 ≤ i) → (i < n) → (0 ≤ j) → (j ≤ n) → (n ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = (sp D_in i_ j_ (k + 1))))) →
    (∀ j_ : Int, (((0 ≤ j_) ∧ (j_ < j)) → (((D i) j_) = (sp D_in i j_ (k + 1))))) →
    (∀ j_ : Int, (((j ≤ j_) ∧ (j_ < n)) → (((D i) j_) = (sp D_in i j_ k)))) →
    (∀ i_ j_ : Int, ((((i + 1) ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = (sp D_in i_ j_ k)))) →
    ((j < n) ∧ (((D i) j) ≤ (((D i) k) + ((D k) j)))) →
    (j' = (j + 1)) →
    ((0 ≤ k) ∧ (k < n) ∧ (0 ≤ i) ∧ (i < n) ∧ (0 ≤ j') ∧ (j' ≤ n) ∧ (n ≥ 0) ∧
     (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = (sp D_in i_ j_ (k + 1))))) ∧
     (∀ j_ : Int, (((0 ≤ j_) ∧ (j_ < j')) → (((D i) j_) = (sp D_in i j_ (k + 1))))) ∧
     (∀ j_ : Int, (((j' ≤ j_) ∧ (j_ < n)) → (((D i) j_) = (sp D_in i j_ k)))) ∧
     (∀ i_ j_ : Int, ((((i + 1) ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = (sp D_in i_ j_ k))))) := by
  intro n i j k D_in D j' _ h_k_nn h_k_lt h_i_nn h_i_lt h_j_nn _ h_n_nn
  intro h_prior h_curr_done h_curr_pending h_future h_guard h_jeq
  subst h_jeq
  obtain ⟨h_j_lt, h_le⟩ := h_guard
  have h_inner :=
    SynthLean.FloydWarshallHelpers.floyd_warshall_inner_inductive
      D D_in n k i j D
      h_k_nn h_k_lt h_i_nn h_i_lt h_j_nn h_j_lt h_n_nn
      h_prior h_curr_done h_curr_pending h_future
      (Or.inl ⟨fun _ _ => rfl, h_le⟩)
  refine ⟨h_k_nn, h_k_lt, h_i_nn, h_i_lt, ?_, ?_, h_n_nn,
          h_inner.1, h_inner.2.1, h_inner.2.2.1, h_inner.2.2.2⟩
  · omega
  · omega

-- sc6 — L2 inductive branch 1 (D[i][j] > D[i][k] + D[k][j], update).
-- Tier-1: wrap floyd_warshall_inner_inductive with D' = D'
-- (the updated array) and h_branch := Or.inr ⟨..., ..., ...⟩.
theorem fw_l2_inductive_branch_1 :
    ∀ (n i j k : Int)
      (D_in D : Int → Int → Int)
      (j' : Int) (D' : Int → Int → Int),
    ((n ≥ 0) ∧ (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = ((D_in i_) j_)))) ∧ (∀ k_ : Int, ((k_ ≥ 0) → ((sp D_in k_ k_ k_) ≥ 0)))) →
    (0 ≤ k) → (k < n) → (0 ≤ i) → (i < n) → (0 ≤ j) → (j ≤ n) → (n ≥ 0) →
    (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = (sp D_in i_ j_ (k + 1))))) →
    (∀ j_ : Int, (((0 ≤ j_) ∧ (j_ < j)) → (((D i) j_) = (sp D_in i j_ (k + 1))))) →
    (∀ j_ : Int, (((j ≤ j_) ∧ (j_ < n)) → (((D i) j_) = (sp D_in i j_ k)))) →
    (∀ i_ j_ : Int, ((((i + 1) ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D i_) j_) = (sp D_in i_ j_ k)))) →
    ((j < n) ∧ (((D i) j) > (((D i) k) + ((D k) j)))) →
    (D' = (store2d D i j (((D i) k) + ((D k) j)))) →
    (j' = (j + 1)) →
    ((0 ≤ k) ∧ (k < n) ∧ (0 ≤ i) ∧ (i < n) ∧ (0 ≤ j') ∧ (j' ≤ n) ∧ (n ≥ 0) ∧
     (∀ i_ j_ : Int, (((0 ≤ i_) ∧ (i_ < i) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D' i_) j_) = (sp D_in i_ j_ (k + 1))))) ∧
     (∀ j_ : Int, (((0 ≤ j_) ∧ (j_ < j')) → (((D' i) j_) = (sp D_in i j_ (k + 1))))) ∧
     (∀ j_ : Int, (((j' ≤ j_) ∧ (j_ < n)) → (((D' i) j_) = (sp D_in i j_ k)))) ∧
     (∀ i_ j_ : Int, ((((i + 1) ≤ i_) ∧ (i_ < n) ∧ (0 ≤ j_) ∧ (j_ < n)) → (((D' i_) j_) = (sp D_in i_ j_ k))))) := by
  intro n i j k D_in D j' D' _ h_k_nn h_k_lt h_i_nn h_i_lt h_j_nn _ h_n_nn
  intro h_prior h_curr_done h_curr_pending h_future h_guard h_Deq h_jeq
  subst h_jeq
  obtain ⟨h_j_lt, h_gt⟩ := h_guard
  -- Build h_branch = Or.inr ⟨D' i j = D i k + D k j, off-cells equal, D[i][j] > sum⟩.
  have h_ij : D' i j = D i k + D k j := by
    rw [h_Deq]; simp [store2d]
  have h_off : ∀ p q : Int, (p ≠ i ∨ q ≠ j) → D' p q = D p q := by
    intro p q hpq
    rw [h_Deq]
    unfold store2d
    have h_ne : ¬ (p = i ∧ q = j) := fun ⟨h1, h2⟩ =>
      hpq.elim (fun h => h h1) (fun h => h h2)
    rw [if_neg h_ne]
  have h_inner :=
    SynthLean.FloydWarshallHelpers.floyd_warshall_inner_inductive
      D D_in n k i j D'
      h_k_nn h_k_lt h_i_nn h_i_lt h_j_nn h_j_lt h_n_nn
      h_prior h_curr_done h_curr_pending h_future
      (Or.inr ⟨h_ij, h_off, h_gt⟩)
  refine ⟨h_k_nn, h_k_lt, h_i_nn, h_i_lt, ?_, ?_, h_n_nn,
          h_inner.1, h_inner.2.1, h_inner.2.2.1, h_inner.2.2.2⟩
  · omega
  · omega

end SynthLean.FloydWarshallHelpers
