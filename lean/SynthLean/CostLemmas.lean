/-
SynthLean.CostLemmas — the resource-bound-invariant Lean library.

Companion to `COST_INVS.md` (the design plan).  The synth framework
emits three cost obligations per cost-bound Loop:
  (A) cost-lb       : τ ⇒ cost@L ≥ 0
  (B) cost-decrement: τ ∧ g ∧ trans ⇒ cost@L(pre) ≥ body_cost + cost@L(post)
  (C) cost-budget   : Pre ∧ chain-prefix ⇒ cost@L(entry) ≤ cost_target

For LINEAR cost expressions Z3 omega handles all three trivially.
For QUADRATIC and higher cost expressions, the cost-decrement
(B) becomes a polynomial-arithmetic check.  Encoding lesson #56
documented the 12× Z3-NIA tax on bubble_sort_cost; this module
gives Lean alternatives (`nlinarith` / `ring`) that close such
obligations cheaply.

The lemmas here are **abstract polynomial identities** — not tied
to any specific benchmark — that arise in the cost-decrement
proofs for common algorithm shapes.  Each one is an
ALGEBRAIC FACT the framework can cite during dispatch.

Wiring into synth dispatch is the next slice; this module just
authors the lemmas and verifies they compile.
-/
import Mathlib.Tactic

namespace SynthLean.CostLemmas

/-! ### Linear cost identities

These are trivially provable by omega; included here for parity
with the lemma library so dispatch logic can uniformly cite a
named theorem. -/

/-- Linear cost decrement: `(n - i) - (n - (i + 1)) = 1`.  The
    canonical sum_array / sumi cost-decrement shape. -/
theorem linear_decrement (n i : Int) :
    (n - i) - (n - (i + 1)) = 1 := by
  ring

set_option linter.unusedVariables false in
/-- Linear cost lower bound at loop entry: if `0 ≤ i ≤ n`, then
    `n - i ≥ 0`.  Used to discharge (A) cost-lb. -/
theorem linear_cost_nonneg (n i : Int) (h0 : 0 ≤ i) (h1 : i ≤ n) :
    (n - i) ≥ 0 := by
  omega

/-- Linear cost budget: at entry (i = 0), `n - i = n` matches the
    target `n`.  Trivial but cited for symmetry. -/
theorem linear_cost_budget_tight (n : Int) :
    (n - 0) = n := by
  ring


/-! ### Quadratic cost identities

The key §1.5 nested-loop result: a quadratic cost expression
decreases per outer iteration by an amount that bounds the
inner-loop iteration count plus the per-iter SB cost. -/

/-- Bubble-sort-style cost-decrement step.

    `cost@L0 = (n - i) * (n - i + 1)`.  Per outer iteration,
    the decrement is:
      `(n - i)(n - i + 1) - (n - i - 1)(n - i) = 2 * (n - i)`.
    This is ≥ `(n - 1 - i) + 2` for `i < n`, i.e., the bound
    dominates the body cost (inner iter count + 2 SBs). -/
theorem bubble_sort_quad_decrement (n i : Int) :
    (n - i) * (n - i + 1) - (n - i - 1) * (n - i) = 2 * (n - i) := by
  ring

/-- The above decrement dominates the inner-loop iteration count
    plus the two surrounding SB costs (j-init and i-step), provided
    we're inside the outer guard `i < n`.  `2 * (n - i) ≥ (n - 1 - i)
    + 2` simplifies to `n - i ≥ 1` which is the outer guard. -/
theorem bubble_sort_decrement_dominates_body (n i : Int)
    (h_guard : i < n) :
    2 * (n - i) ≥ (n - 1 - i) + 2 := by
  omega

/-- General-purpose quadratic-cost decrement, parameterized by
    the outer per-iteration cost `c`.  When `cost@L = (n - i) * c`
    for a positive constant `c`, the per-iter decrement is `c`. -/
theorem quadratic_outer_decrement (n i c : Int) :
    (n - i) * c - (n - (i + 1)) * c = c := by
  ring


/-! ### Nested-loop cost composition

For an outer loop running `n - i` more iterations, each costing
the inner loop's total cost plus surrounding SB cost, the total
remaining cost matches the cost@L0 quadratic candidate.

These lemmas formalize the inductive shape used in §1.5's
`cost-decrement` constraint, which the synth framework emits
automatically.  Lean dispatch can cite the relevant identity
when Z3's NIA wedges. -/

/-- Outer cost-decrement for a nested loop where the inner cost
    at body entry is `n - 1 - i` (e.g., bubble_sort).

    Outer body cost = inner cost + 2 SBs = (n - 1 - i) + 2.
    Outer cost candidate: `(n - i) * (n - i + 1)`, per-iter
    decrement: `2 * (n - i)`.
    Check: `2 * (n - i) ≥ (n - 1 - i) + 2` for `i < n`. -/
theorem nested_loop_bubble_admissible (n i : Int) (h_guard : i < n) :
    (n - i) * (n - i + 1) - (n - i - 1) * (n - i)
      ≥ (n - 1 - i) + 2 := by
  have h1 : (n - i) * (n - i + 1) - (n - i - 1) * (n - i)
              = 2 * (n - i) := by ring
  rw [h1]
  omega

/-- Outer cost-decrement for a nested loop where the inner cost
    at body entry is a CONSTANT `m` (e.g., nested_loop benchmark
    where inner runs `n` times regardless of outer i).

    Outer body cost = inner cost + 2 SBs = m + 2.
    Outer cost candidate: `(n - i) * (m + 2)`, per-iter decrement
    is exactly `m + 2`. -/
theorem nested_loop_constant_inner_admissible (n m i : Int) :
    (n - i) * (m + 2) - (n - (i + 1)) * (m + 2) = m + 2 := by
  ring


/-! ### Cost-budget closed forms

When the synthesizer searches for a cost@L candidate that
dominates `cost_target`, the (C) cost-budget obligation
requires `cost@L(entry) ≤ cost_target(input)`.  For quadratic
costs, this is a polynomial inequality that may be tight. -/

/-- For `cost@L = (n - i) * (n - i + 1)` evaluated at the outer
    loop's initial state (i = 0): `cost@L(0) = n * (n + 1)`.
    Used to discharge (C) cost-budget when `cost_target = "n * (n + 1)"`. -/
theorem bubble_sort_budget_initial (n : Int) :
    (n - 0) * (n - 0 + 1) = n * (n + 1) := by
  ring

/-- For `cost@L = (n - i) * (n + 2)` evaluated at i = 0:
    `cost@L(0) = n * (n + 2)`.  Used in nested_cost.py. -/
theorem nested_loop_budget_initial (n : Int) :
    (n - 0) * (n + 2) = n * (n + 2) := by
  ring


/-! ### General-purpose cost-monotonicity helpers

These are abstract claims about cost functions that decrease
monotonically; the framework emits the corresponding constraints
automatically, so these are mostly cited for parity. -/

/-- If `cost(state)` decreases by at least `body_cost` per
    iteration and starts at `K`, then the total iteration count
    is bounded by `K / body_cost`.  Stated as the well-known
    "ranking → bounded iteration count" lemma. -/
theorem cost_bounds_iter_count (K body_cost : Int)
    (h_K  : K ≥ 0)
    (h_bc : body_cost ≥ 1) :
    ∃ B : Int, B ≥ 0 ∧ B * body_cost ≥ K := by
  -- Trivial: B = K satisfies both (since body_cost ≥ 1).
  refine ⟨K, h_K, ?_⟩
  -- K * body_cost ≥ K when body_cost ≥ 1 and K ≥ 0.
  nlinarith


end SynthLean.CostLemmas
