/-
kadane_max_subarray Tier-3 helpers — RESEARCH.md §H.1.

Unlike majority_element's classical Boyer-Moore correctness
(which needed a documented axiom), kadane's bundle-post is
ENTIRELY PROVABLE from the user's stated τ atoms.  The user's
"best upper bound" invariant atom at loop exit (i = n) IS the
post.

This is the Tier-1 quality of Tier-3: ONE algorithm-correctness
theorem captured cleanly, proved from user axioms with no
trust-point axioms.  Shim files citing this helper get a
~4-line proof body.
-/
import SynthLean.Basic
open SynthLean

axiom sum_range : (Int → Int) → Int → Int → Int
axiom kadane_user_axiom_0 : ∀ (A : Int → Int), (∀ p : Int, ((sum_range A p p) = 0))
axiom kadane_user_axiom_1 : ∀ (A : Int → Int), (∀ p q : Int, ((p ≤ q) → ((sum_range A p (q + 1)) = ((sum_range A p q) + (A q)))))

/-
Classical Kadane invariant preservation, encoded as TWO named
Tier-2 axioms (one per SB(n=2) branch).

The user's τ atoms at L0 are:
  0: 1 ≤ i
  1: i ≤ n
  2: ∀ p. 0 ≤ p ≤ i-1 → sum_range A p i ≤ cur
  3: ∃ p. 0 ≤ p ≤ i-1 ∧ sum_range A p i = cur
  4: ∀ p, q. 0 ≤ p ≤ q < i → sum_range A p (q+1) ≤ best
  5: best ≥ cur

For each branch (extending vs restarting), the algorithm
correctness claim is that ALL six conjuncts are preserved
after the body executes.  Proofs of these axioms reduce to:
  - axiom 0 (sum_range A p p = 0)
  - axiom 1 (sum_range A p (q+1) = sum_range A p q + A[q])
  - case-split on p < i vs p = i in the extended range
  - if-then-else dispatch on the best update

Future work: replace these axioms with explicit Lean proofs.
For now, the Tier-2 trust scope is the algorithm's correctness
claim per branch — same precedent as boyer_moore_dominance in
majority_element and sp_self_nonneg in floyd_warshall.
-/
-- Tier-1: branch 0 = extending (cur ≥ 0).  Uses sum_range
-- recurrence (axiom_1) to extend p-to-i+1 sums.  Edge case p=i
-- via axiom_0 (sum_range A p p = 0) + cur ≥ 0 from guard.
theorem kadane_branch0_preserves_inv :
    ∀ (A : Int → Int) (n best cur i best' cur' i' : Int),
      n ≥ 1 →
      (1 ≤ i) →
      (i ≤ n) →
      (∀ p : Int, ((0 ≤ p) ∧ (p ≤ (i - 1))) →
                  ((sum_range A p i) ≤ cur)) →
      (∃ p : Int, (0 ≤ p) ∧ (p ≤ (i - 1)) ∧
                  ((sum_range A p i) = cur)) →
      (∀ p q : Int,
        ((0 ≤ p) ∧ (p ≤ q) ∧ (q < i)) →
        ((sum_range A p (q + 1)) ≤ best)) →
      (best ≥ cur) →
      ((i < n) ∧ ((cur + (A i)) ≥ (A i))) →
      (cur' = (cur + (A i))) →
      (best' = (if (best ≥ (cur + (A i))) then best
                else (cur + (A i)))) →
      (i' = (i + 1)) →
      ((1 ≤ i')) ∧ ((i' ≤ n)) ∧
      ((∀ p : Int, ((0 ≤ p) ∧ (p ≤ (i' - 1))) →
                   ((sum_range A p i') ≤ cur'))) ∧
      ((∃ p : Int, (0 ≤ p) ∧ (p ≤ (i' - 1)) ∧
                   ((sum_range A p i') = cur'))) ∧
      ((∀ p q : Int,
        ((0 ≤ p) ∧ (p ≤ q) ∧ (q < i')) →
        ((sum_range A p (q + 1)) ≤ best'))) ∧
      ((best' ≥ cur')) := by
  intro A n best cur i best' cur' i' _ h_i_ge h_i_le
  intro h_cur_ub h_cur_lb h_best_ub h_best_ge_cur h_guard
  intro h_cur_eq h_best_eq h_i_eq
  subst h_cur_eq h_i_eq
  obtain ⟨h_i_lt, h_cur_nn⟩ := h_guard
  have h_cur_ge_zero : cur ≥ 0 := by linarith
  -- Key: sum_range A p (i+1) = sum_range A p i + A i  (axiom_1 with p ≤ i).
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  -- Conjunct 3: ∀ p ∈ [0, i].  sum_range(A, p, i+1) ≤ cur + A[i].
  · intro p ⟨h_p0, h_p_le⟩
    have h_step : sum_range A p (i + 1) = sum_range A p i + A i :=
      kadane_user_axiom_1 A p i (by omega)
    rw [h_step]
    by_cases hp : p = i
    · rw [hp, kadane_user_axiom_0 A i]; linarith
    · have h_p_le' : p ≤ i - 1 := by omega
      have := h_cur_ub p ⟨h_p0, h_p_le'⟩
      linarith
  -- Conjunct 4: ∃ p ∈ [0, i].  sum_range(A, p, i+1) = cur + A[i].
  · obtain ⟨p, h_p0, h_p_le, h_eq⟩ := h_cur_lb
    refine ⟨p, h_p0, by omega, ?_⟩
    have h_step : sum_range A p (i + 1) = sum_range A p i + A i :=
      kadane_user_axiom_1 A p i (by omega)
    rw [h_step, h_eq]
  -- Conjunct 5: ∀ p q ∈ [0, i].  sum_range(A, p, q+1) ≤ best'.
  · intro p q ⟨h_p0, h_p_le_q, h_q_lt⟩
    by_cases hq : q < i
    · have := h_best_ub p q ⟨h_p0, h_p_le_q, hq⟩
      by_cases hb : best ≥ cur + A i
      · rw [h_best_eq]; simp [hb]; linarith
      · rw [h_best_eq]; simp [hb]; linarith
    · have h_q_eq : q = i := by omega
      rw [h_q_eq]
      have h_step : sum_range A p (i + 1) = sum_range A p i + A i :=
        kadane_user_axiom_1 A p i (by omega)
      rw [h_step]
      by_cases hp : p = i
      · rw [hp, kadane_user_axiom_0 A i]
        by_cases hb : best ≥ cur + A i
        · rw [h_best_eq]; simp [hb]; omega
        · rw [h_best_eq]; simp [hb]; omega
      · have h_p_le' : p ≤ i - 1 := by omega
        have h_sr_le := h_cur_ub p ⟨h_p0, h_p_le'⟩
        have h_total : sum_range A p i + A i ≤ cur + A i := by linarith
        by_cases hb : best ≥ cur + A i
        · rw [h_best_eq]; simp [hb]; omega
        · rw [h_best_eq]; simp [hb]; exact h_sr_le
  -- Conjunct 6: best' ≥ cur'.
  · rw [h_best_eq]
    by_cases hb : best ≥ cur + A i
    · simp [hb]
    · simp [hb]

-- Tier-1: branch 1 = restarting (cur < 0, cur' = A[i]).
-- Same structure as branch_0 but cur' = A[i] instead of cur + A[i].
theorem kadane_branch1_preserves_inv :
    ∀ (A : Int → Int) (n best cur i best' cur' i' : Int),
      n ≥ 1 →
      (1 ≤ i) →
      (i ≤ n) →
      (∀ p : Int, ((0 ≤ p) ∧ (p ≤ (i - 1))) →
                  ((sum_range A p i) ≤ cur)) →
      (∃ p : Int, (0 ≤ p) ∧ (p ≤ (i - 1)) ∧
                  ((sum_range A p i) = cur)) →
      (∀ p q : Int,
        ((0 ≤ p) ∧ (p ≤ q) ∧ (q < i)) →
        ((sum_range A p (q + 1)) ≤ best)) →
      (best ≥ cur) →
      ((i < n) ∧ ((cur + (A i)) < (A i))) →
      (cur' = (A i)) →
      (best' = (if (best ≥ (A i)) then best else (A i))) →
      (i' = (i + 1)) →
      ((1 ≤ i')) ∧ ((i' ≤ n)) ∧
      ((∀ p : Int, ((0 ≤ p) ∧ (p ≤ (i' - 1))) →
                   ((sum_range A p i') ≤ cur'))) ∧
      ((∃ p : Int, (0 ≤ p) ∧ (p ≤ (i' - 1)) ∧
                   ((sum_range A p i') = cur'))) ∧
      ((∀ p q : Int,
        ((0 ≤ p) ∧ (p ≤ q) ∧ (q < i')) →
        ((sum_range A p (q + 1)) ≤ best'))) ∧
      ((best' ≥ cur')) := by
  intro A n best cur i best' cur' i' _ h_i_ge h_i_le
  intro h_cur_ub _ h_best_ub h_best_ge_cur h_guard
  intro h_cur_eq h_best_eq h_i_eq
  subst h_cur_eq h_i_eq
  obtain ⟨h_i_lt, h_cur_neg⟩ := h_guard
  have h_cur_lt_zero : cur < 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  -- Conjunct 3: ∀ p ∈ [0, i]. sum_range(A, p, i+1) ≤ A[i].
  · intro p ⟨h_p0, h_p_le⟩
    have h_step : sum_range A p (i + 1) = sum_range A p i + A i :=
      kadane_user_axiom_1 A p i (by omega)
    rw [h_step]
    by_cases hp : p = i
    · rw [hp, kadane_user_axiom_0 A i]; linarith
    · have h_p_le' : p ≤ i - 1 := by omega
      have := h_cur_ub p ⟨h_p0, h_p_le'⟩; linarith
  -- Conjunct 4: ∃ p = i with sum_range = A[i].
  · refine ⟨i, by omega, by omega, ?_⟩
    rw [kadane_user_axiom_1 A i i (le_refl _), kadane_user_axiom_0 A i]; ring
  -- Conjunct 5: best' bound.
  · intro p q ⟨h_p0, h_p_le_q, h_q_lt⟩
    by_cases hq : q < i
    · have := h_best_ub p q ⟨h_p0, h_p_le_q, hq⟩
      by_cases hb : best ≥ A i
      · rw [h_best_eq]; simp [hb]; linarith
      · rw [h_best_eq]; simp [hb]; linarith
    · have h_q_eq : q = i := by omega
      rw [h_q_eq]
      have h_step : sum_range A p (i + 1) = sum_range A p i + A i :=
        kadane_user_axiom_1 A p i (by omega)
      rw [h_step]
      by_cases hp : p = i
      · rw [hp, kadane_user_axiom_0 A i]
        by_cases hb : best ≥ A i
        · rw [h_best_eq]; simp [hb]
        · rw [h_best_eq]; simp [hb]
      · have h_p_le' : p ≤ i - 1 := by omega
        have h_sr_le := h_cur_ub p ⟨h_p0, h_p_le'⟩
        by_cases hb : best ≥ A i
        · rw [h_best_eq]; simp [hb]; linarith
        · rw [h_best_eq]; simp [hb]; linarith
  -- Conjunct 6: best' ≥ cur' = A[i].
  · rw [h_best_eq]
    by_cases hb : best ≥ A i
    · simp [hb]
    · simp [hb]

namespace SynthLean.KadaneHelpers

/-
Bundle-post helper (kind = safety-bundle-post).

Given the loop-exit state (i = n via the negated guard) with
the user's "best upper bound" invariant, derive the post:

    ∀ p q. 0 ≤ p ≤ q < n → sum_range(A, p, q+1) ≤ best

Required τ atoms (any τ-subset MUST include all of these):
  - i_le_n:   i ≤ n
  - best_ub:  ∀ p, q. 0 ≤ p ≤ q < i → sum_range(A, p, q+1) ≤ best

Plus the loop-exit hypothesis:
  - h_not_g:  ¬ (i < n)

Proof: at loop exit, i = n.  The user's best-upper-bound atom
at i = n IS the post — substitute i = n into the atom.

No trust-point axiom needed; this is provable entirely from
the user's stated atoms.
-/
theorem kadane_post_from_inv
    (A : Int → Int) (n best i : Int)
    (h_i_le_n : i ≤ n)
    (h_best_ub : ∀ p q : Int,
                   ((0 ≤ p) ∧ (p ≤ q) ∧ (q < i)) →
                   (sum_range A p (q + 1) ≤ best))
    (h_not_g : ¬ (i < n)) :
    ∀ p q : Int,
      ((0 ≤ p) ∧ (p ≤ q) ∧ (q < n)) →
      (sum_range A p (q + 1) ≤ best) := by
  have h_i_eq : i = n := by omega
  intro p q hpq
  apply h_best_ub p q
  obtain ⟨h0, h1, h2⟩ := hpq
  exact ⟨h0, h1, by omega⟩

end SynthLean.KadaneHelpers
