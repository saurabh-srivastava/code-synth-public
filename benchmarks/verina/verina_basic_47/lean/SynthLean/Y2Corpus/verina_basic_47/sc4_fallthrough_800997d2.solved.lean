/-
verina_basic_47 (arraySum) — chain-bundle (post) obligation for chosen
τ = {0 ≤ i, i ≤ n, result = sum(A, i)}.

At loop exit (through the trailing no-op SB, which preserves all vars):
from h_tau_1 (i' ≤ n) ∧ h_not_g (¬(i' < n)) ∧ h_tau_0 (0 ≤ i'): i' = n.
Substitute into h_tau_2: result' = sum(A, i') = sum(A, n).

This is exactly VERINA's post `result = sumTo a a.size` (our `sum`
re-axiomatizes VERINA's `sumTo`; see the benchmark docstring).
-/
import SynthLean.Core
open SynthLean

axiom sum : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((sum A 0) = 0)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ (k : Int),
    ((k ≥ 0) → ((sum A (k + 1)) = ((sum A k) + (A k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n result i : Int)
    (A : Int → Int)
    (result' i' : Int)
    (h_pre : (n ≥ 1))
    (h_tau_0 : (0 ≤ i'))
    (h_tau_1 : (i' ≤ n))
    (h_tau_2 : (result' = (sum A i')))
    (h_not_g : ¬ ((i' < n))) :
    (result' = (sum A n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_2

end SynthLean.VerifyTmp
