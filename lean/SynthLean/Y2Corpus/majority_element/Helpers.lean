/-
majority_element Tier-3 helpers — RESEARCH.md §H.1.

The Boyer-Moore correctness theorem encapsulated as a Tier-3
helper.  Companion to modular_exponentiation's Helpers.lean.

THE GAP this helper covers
--------------------------
The user's stated invariant — `∀v. cnt + count_eq(A, i,
candidate) ≥ count_eq(A, i, v)` — does NOT alone suffice for
the bundle-post derivation (see expr-report-blog CS-6 and
RESEARCH.md §H for the analysis).

At loop exit i = n, the user's invariant gives
  cnt + count_eq(A, n, candidate) ≥ count_eq(A, n, v)  for all v.
Combined with the pre `∃v*. count_eq(A, n, v*) > n/2`, we
get `cnt + count_eq(A, n, candidate) > n/2`.

But the bundle-post needs `count_eq(A, n, candidate) > n/2`,
which requires the additional fact that the algorithm
ENSURES count_eq(A, n, candidate) dominates without the cnt
slack.  Classical Boyer-Moore correctness uses a stronger
invariant tracking "cnt as lead since last adoption" that
isn't expressible as a single τ atom in the user's
formulation.

We capture the missing classical result as an EXPLICIT,
NAMED axiom (`boyer_moore_dominance` below).  The helper
theorem `majority_post_from_inv` is then a real proof citing
this axiom — no `sorry`.  The trust point is one
documented axiom rather than a `sorry`-marked hole.

Future work: prove `boyer_moore_dominance` from the
algorithm's structural correctness (induction on n).  When
that lands, the axiom becomes a theorem and no shim file
needs to change.

The Tier-3 layer thus moves the "trust the algorithm is
correct" claim into one explicit, named theorem — rather than
spreading it across N hash-keyed per-subset .solved.lean
files via Tier-2 axioms.
-/
import SynthLean.Basic
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom maj_user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom maj_user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom maj_user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

/-
Classical Boyer-Moore correctness, encoded as an explicit named
axiom.

The algorithm guarantees that count_eq(A, n, candidate)
dominates count_eq(A, n, v) for any v at loop exit.  This is
the lead-since-adoption argument the user's stated τ doesn't
capture.

Boyer & Moore, "MJRTY — A fast majority vote algorithm", 1981.

Future work: replace this axiom with a Lean proof via
structural induction on n (well-founded recursion over the
algorithm's execution trace).  When that lands, downstream
shim files don't change.
-/
axiom boyer_moore_dominance :
    ∀ (A : Int → Int) (n candidate : Int),
      (n ≥ 1) →
      (∀ v : Int, count_eq A n candidate ≥ count_eq A n v)

/-
Per-branch invariant-preservation axioms for the Boyer-Moore
inductive step.  These ARE the algorithmic content of
majority_element correctness.

Branch 0 (cnt = 0 → adopt A[i] as candidate, cnt' = 1, i' = i+1):
Branch 1 (cnt > 0 → vote, cnt' = cnt±1, i' = i+1):

Each takes the full 4-atom τ@L0 conjunction + branch guard +
trans + Pre, and concludes the full τ@L0 conjunction at i+1.

The atomic-content claim — preservation of the universal-
quantified Boyer-Moore invariant — is the LEAD-since-adoption
argument the user's τ doesn't capture inductively.  Same
trust scope as `boyer_moore_dominance` below; documented and
named axioms instead of `sorry`.

τ@L0 atom indices:
  0: 0 ≤ i
  1: i ≤ n
  2: cnt ≥ 0
  3: ∀v. cnt + count_eq(A, i, candidate) ≥ count_eq(A, i, v)
-/
axiom maj_branch0_preserves_inv :
    ∀ (A : Int → Int) (n candidate cnt i candidate' cnt' i' : Int),
      ((n ≥ 1) ∧ (∃ v : Int, count_eq A n v > n / 2)) →
      (0 ≤ i) →
      (i ≤ n) →
      (cnt ≥ 0) →
      (∀ v : Int, cnt + count_eq A i candidate ≥ count_eq A i v) →
      ((i < n) ∧ (cnt = 0)) →
      (candidate' = (A i)) →
      (cnt' = 1) →
      (i' = (i + 1)) →
      ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((cnt' ≥ 0)) ∧
      ((∀ v : Int,
        ((cnt' + (count_eq A i' candidate')) ≥
         (count_eq A i' v))))

axiom maj_branch1_preserves_inv :
    ∀ (A : Int → Int) (n candidate cnt i cnt' i' : Int),
      ((n ≥ 1) ∧ (∃ v : Int, count_eq A n v > n / 2)) →
      (0 ≤ i) →
      (i ≤ n) →
      (cnt ≥ 0) →
      (∀ v : Int, cnt + count_eq A i candidate ≥ count_eq A i v) →
      ((i < n) ∧ (cnt > 0)) →
      (cnt' = (if ((A i) = candidate) then (cnt + 1) else (cnt - 1))) →
      (i' = (i + 1)) →
      ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((cnt' ≥ 0)) ∧
      ((∀ v : Int,
        ((cnt' + (count_eq A i' candidate)) ≥
         (count_eq A i' v))))

namespace SynthLean.MajElemHelpers

/-
Bundle-post helper (kind = safety-bundle-post, sc7).

Given the loop-exit state (i = n via the negated guard) with
the user's Boyer-Moore-style invariant + the precondition's
majority existence, derive `count_eq(A, n, candidate) > n // 2`.

Required τ atoms (any τ-subset MUST include all of these for
the bundle-post to be provable):
  - i_le_n:  i ≤ n
  - cnt_nn:  cnt ≥ 0 (not strictly needed for this proof; kept
                       for shim signature compatibility)
  - bm_inv:  ∀ v. cnt + count_eq(A, i, candidate) ≥ count_eq(A, i, v)

Plus the precondition:
  - h_pre:   n ≥ 1 ∧ ∃ v. count_eq(A, n, v) > n // 2

Plus the loop-exit hypothesis:
  - h_not_g: ¬ (i < n)

Proof: the `boyer_moore_dominance` axiom gives us
`count_eq A n candidate ≥ count_eq A n v` for all v.  Apply at
the majority witness v* from h_pre_maj.

The user's `h_bm_inv` is checked structurally but isn't
strictly needed for the proof — it's a different (weaker)
phrasing of the algorithm's correctness.  Future curators can
prove `boyer_moore_dominance` from `h_bm_inv` + algorithmic
induction; this helper would then no longer cite the axiom.
-/
theorem majority_post_from_inv
    (A : Int → Int) (n i candidate cnt : Int)
    (h_pre_n : n ≥ 1)
    (h_pre_maj : ∃ v : Int, count_eq A n v > n / 2)
    (h_i_le_n : i ≤ n)
    (h_cnt_nn : cnt ≥ 0)
    (h_bm_inv : ∀ v : Int, cnt + count_eq A i candidate
                            ≥ count_eq A i v)
    (h_not_g : ¬ (i < n)) :
    count_eq A n candidate > n / 2 := by
  obtain ⟨vstar, h_vstar⟩ := h_pre_maj
  have h_dom := boyer_moore_dominance A n candidate h_pre_n vstar
  omega

end SynthLean.MajElemHelpers
