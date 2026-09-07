/-
SynthLean.Basic — mathlib-backed extensions of Core.

`SynthLean.Core` has the lightweight defs (`store`, `store2d`)
without mathlib.  This module imports Core + `Mathlib.Tactic`
for the tactic palette (`ring`, `nlinarith`, `linarith`,
`aesop`, etc.) that the generic tactic chain depends on.

Day 4 brought mathlib in for the nonlinear safety-inductive
obligations (sumi's `2*s = i*(i+1)`).  The Core split is
perf/trivial-helpers work — trivial proofs that need only
`omega`/`subst_eqs`/citation skip importing this module to
save ~3s of mathlib preload per `lake env lean` call.
-/
import SynthLean.Core
import Mathlib.Tactic

namespace SynthLean
-- `store` / `store2d` are re-exported via `import SynthLean.Core`
-- so existing code that imports `SynthLean.Basic` and references
-- `store` continues to work.

/-- The literal smoke test from `RESEARCH.LEAN.md` §7. -/
example : 1 + 1 = 2 := rfl

/-- A tactic-based proof — we'll be building lots of these. -/
example (n : Nat) : n + 0 = n := by
  simp

/-- A universally-quantified Nat statement: closest shape to
    our actual proof obligations (∀-quantified over program
    variables). -/
example : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

/-- Conditional implication — mirrors safety-constraint shape
    (`τ ∧ guard ⇒ post`). -/
example (n : Nat) (h : n > 0) : n - 1 + 1 = n := by
  omega

-- `store` is now defined in `SynthLean.Core` (no mathlib).
-- Re-exposed via the namespace open here.

example (A : Int → Int) (i : Int) (v : Int) :
    (store A i v) i = v := by
  simp [store]

example (A : Int → Int) (i j : Int) (v : Int) (hne : i ≠ j) :
    (store A i v) j = A j := by
  simp [store, hne.symm]

/-- mathlib smoke test #1: `ring` discharges polynomial identities.
    This is the shape `theorem_for_safety_inductive` produces for
    sumi's nonlinear inductive (`2*s' = i'*(i'+1)`). -/
example (s i s' i' : Int)
    (h_tau : 2 * s = i * (i + 1))
    (h_s' : s' = s + i + 1)
    (h_i' : i' = i + 1) :
    2 * s' = i' * (i' + 1) := by
  subst h_s' h_i'
  linarith [sq_nonneg (i + 1)]   -- or just `linarith` after expansion
  -- alternative one-liner: nlinarith [h_tau]

/-- mathlib smoke test #2: `nlinarith` for nonlinear ranking
    decreases like intsqrt's `(i - 1)² < i² ← i ≥ 1`. -/
example (i : Int) (h : i ≥ 1) : (i - 1) * (i - 1) < i * i := by
  nlinarith

-- `store2d` is now defined in `SynthLean.Core` (no mathlib).

example (A : Int → Int → Int) (i j : Int) (v : Int) :
    (store2d A i j v) i j = v := by
  simp [store2d]

example (A : Int → Int → Int) (i j p q : Int) (v : Int)
    (hne : ¬ (p = i ∧ q = j)) :
    (store2d A i j v) p q = A p q := by
  simp [store2d, hne]

end SynthLean
