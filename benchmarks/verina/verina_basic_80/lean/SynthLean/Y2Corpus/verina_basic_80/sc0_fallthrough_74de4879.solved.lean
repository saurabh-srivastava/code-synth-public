/-
verina_basic_80 (only_once) — entry-bundle obligation (sc0).
Init: c := 0, i := 0.  Chosen τ = {c = count_occ(A,key,i),
0 ≤ i, i ≤ n, n ≥ 0}.  The UF-application conjunct
0 = count_occ(A,key,0) is the base axiom read symmetrically
(REC 11.7.A sc0 UF cliff); the three bounds are arithmetic.
-/
import SynthLean.Core
open SynthLean

axiom count_occ : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (key : Int), ((count_occ A key 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) = key)) → ((count_occ A key (k + 1)) = ((count_occ A key k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) ≠ key)) → ((count_occ A key (k + 1)) = (count_occ A key k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc0_fallthrough
    (n key result c i : Int)
    (A : Int → Int)
    (c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_init_c : c' = 0)
    (h_init_i : i' = 0) :
    ((c' = (count_occ A key i'))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) ∧ ((n ≥ 0)) := by
  subst_eqs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (user_axiom_0 A key).symm
  · omega
  · omega
  · omega

end SynthLean.VerifyTmp
