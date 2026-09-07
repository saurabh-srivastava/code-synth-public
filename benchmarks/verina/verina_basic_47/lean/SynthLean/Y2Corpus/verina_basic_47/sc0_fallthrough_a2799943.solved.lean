/-
verina_basic_47 (arraySum) — entry-bundle obligation for chosen τ =
{0 ≤ i, i ≤ n, result = sum(A, i)}.

After the init SB (result := 0, i := 0), establish τ at loop entry:
  1. 0 ≤ 0            — omega.
  2. 0 ≤ n            — omega from h_pre (n ≥ 1).
  3. 0 = sum(A, 0)    — user_axiom_0 (symm): our `sum` re-axiomatizes
     VERINA's `sumTo`, whose base case is `sumTo a 0 = 0`.

REC 11.7.A / F14: entry-bundle τ contains a UF application equation
(`result = sum(A, i)`), so this sc0 companion is authored upfront —
the `0 = sum(A, 0)` conjunct needs a SYMMETRIC rewrite of user_axiom_0
that omega/nlinarith cannot do.
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
theorem sc0_fallthrough
    (n result i : Int)
    (A : Int → Int)
    (result' i' : Int)
    (h_pre : (n ≥ 1))
    (h_init_result : result' = 0)
    (h_init_i : i' = 0) :
    ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((result' = (sum A i'))) := by
  subst h_init_result h_init_i
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · exact (user_axiom_0 A).symm

end SynthLean.VerifyTmp
