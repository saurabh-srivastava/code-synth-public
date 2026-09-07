/-
K.3.2 baby step — sc0 (entry-bundle) at full τ.

After s@B0 (w := 0), prove the loop invariant:
  0 ≤ w' ∧ w' ≤ n ∧ MI(M).

  - 0 ≤ w': w' = 0 from h_init_w.  omega.
  - w' ≤ n: 0 ≤ n from pre, w' = 0, so 0 ≤ n.  omega.
  - MI(M): h_pre's MI atom is at the same position (M unchanged
    by s@B0).  Direct.
-/
import SynthLean.Core
open SynthLean

axiom user_axiom_0 : (0 = 0)
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc0_fallthrough
    (n u v z w : Int)
    (M : Int → Int)
    (G : Int → Int → Int)
    (w' : Int)
    (h_pre : ((n ≥ 0) ∧ (0 ≤ u) ∧ (u < n) ∧ (0 ≤ v) ∧ (v < n) ∧ (0 ≤ z) ∧ (z < n) ∧ (u ≠ v) ∧ (u ≠ z) ∧ (v ≠ z) ∧ (∀ (k : Int), (((0 ≤ k) ∧ (k < n) ∧ ((M k) ≠ (-1))) → ((0 ≤ (M k)) ∧ ((M k) < n)))) ∧ ((M u) = (-1)) ∧ ((M v) = z) ∧ ((M z) = v) ∧ (((G u) v) ≥ 1) ∧ (∀ (p : Int) (q : Int), (((0 ≤ p) ∧ (p < n) ∧ (0 ≤ q) ∧ (q < n)) → (((G p) q) = ((G q) p))))))
    (h_init_w : w' = 0) :
    ((0 ≤ w')) ∧ ((w' ≤ n)) ∧ ((∀ (k : Int), (((0 ≤ k) ∧ (k < n) ∧ ((M k) ≠ (-1))) → ((0 ≤ (M k)) ∧ ((M k) < n))))) := by
  subst h_init_w
  refine ⟨by omega, by omega, ?_⟩
  exact h_pre.2.2.2.2.2.2.2.2.2.2.1
end SynthLean.VerifyTmp
