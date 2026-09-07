/-
SynthLean.CostLemmasSmoke — proof-of-concept smoke test.

Demonstrates that bubble_sort_cost's quadratic cost-decrement
obligation (which pays a 12× Z3-NIA tax in pure-Z3 dispatch)
closes in milliseconds via citation of CostLemmas's named
identities.

Theorem shape (matches what the synth Lean translator would
emit for cost-decrement on bubble_sort_cost's outer loop):

  τ(pre) ∧ g_outer(pre) ∧ trans_body(pre → post)
    ⇒  cost@L0(pre) ≥ body_cost(pre) + cost@L0(post)

For bubble_sort_cost:
  cost@L0(state) = (n - i) * (n - i + 1)
  body_cost = (n - 1 - i) + 2  -- inner Loop runs (n-1-i) iters
                                -- + 2 surrounding SBs (j-init, i-step)
  Outer guard: i < n
-/
import Mathlib.Tactic
import SynthLean.CostLemmas

namespace SynthLean.CostLemmasSmoke

open SynthLean.CostLemmas

set_option linter.unusedVariables false in
/-- bubble_sort_cost outer cost-decrement, discharged via the
    `nested_loop_bubble_admissible` lemma in CostLemmas.

    Note: in the actual translator-emitted theorem, the pre-state
    `i` and post-state `i'` are bound separately with `i' = i + 1`
    via a transition hypothesis.  We inline the substitution for
    clarity here. -/
theorem bubble_sort_outer_decrement
    (n i : Int)
    (h_pre   : n ≥ 0)
    (h_tau_0 : 0 ≤ i)
    (h_tau_1 : i ≤ n)
    (h_guard : i < n) :
    (n - i) * (n - i + 1)
      ≥ ((n - 1 - i) + 2) + (n - (i + 1)) * (n - (i + 1) + 1) := by
  -- Direct citation of the nested-loop admissibility lemma.
  -- Goal restructure: LHS - RHS_of_minus ≥ body_cost.
  have h := nested_loop_bubble_admissible n i h_guard
  -- nested_loop_bubble_admissible gives:
  --   (n - i)(n - i + 1) - (n - i - 1)(n - i) ≥ (n - 1 - i) + 2
  -- We need:
  --   (n - i)(n - i + 1) ≥ ((n - 1 - i) + 2) + (n - i - 1)(n - i)
  -- which is the same after a `ring_nf` reformulation.
  --
  -- Note: `n - (i + 1) = n - i - 1` and
  --       `(n - (i + 1)) * (n - (i + 1) + 1) = (n - i - 1) * (n - i)`.
  have e1 : n - (i + 1) = n - i - 1 := by ring
  have e2 : (n - (i + 1)) * (n - (i + 1) + 1) = (n - i - 1) * (n - i) := by
    ring
  rw [e2]
  linarith


end SynthLean.CostLemmasSmoke
