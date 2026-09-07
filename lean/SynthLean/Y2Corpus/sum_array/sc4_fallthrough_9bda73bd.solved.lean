/-
sum_array's chain-bundle (post) obligation for chosen τ =
{0≤i, i≤n, s = sum(A, i)}.

Argument: from h_tau_1 (i' ≤ n) and h_not_g (¬(i' < n)) and
h_tau_0 (0 ≤ i'): i' = n.  Substitute into h_tau_2:
  s' = sum(A, i') = sum(A, n).
-/
import SynthLean.Core
open SynthLean

axiom sum : (Int → Int) → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), ((sum A 0) = 0)
axiom user_axiom_1 :
  ∀ (A : Int → Int), (∀ k : Int,
    ((k ≥ 0) → ((sum A (k + 1)) = ((sum A k) + (A k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n s i : Int)
    (A : Int → Int)
    (s' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (0 ≤ i'))
    (h_tau_1 : (i' ≤ n))
    (h_tau_2 : (s' = (sum A i')))
    (h_not_g : ¬ ((i' < n))) :
    (s' = (sum A n)) := by
  have h_i : i' = n := by omega
  rw [← h_i]; exact h_tau_2

end SynthLean.VerifyTmp
