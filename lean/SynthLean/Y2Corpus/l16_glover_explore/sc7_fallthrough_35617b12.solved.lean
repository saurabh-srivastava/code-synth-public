/-
Slice A sc7 post-bundle for l16_glover_explore, chosen τ =
{is_valid_pm, 0≤i, i≤n}.

After ¬g (n ≤ i') and h_tau_2 (i' ≤ n): i' = n.  Substitute
into h_tau_0 to get is_valid_pm G n n M' = 1, then apply
user_axiom_1 (termination axiom in this benchmark's axiom
ordering) to derive is_max_matching G n M' = 1.

Same proof shape as bench_glover_verify's sc7 helper; just
remapped to the new axiom indices because this benchmark has
more UFs (3 step variants) and reordered axioms.
-/
import SynthLean.Core
open SynthLean

axiom is_valid_pm : Int → Int → Int → Int → Int
axiom is_max_matching : Int → Int → Int → Int
axiom empty_matching : Int
axiom step_glover : Int → Int → Int → Int
axiom step_greedy_first : Int → Int → Int → Int
axiom step_bucket_assign : Int → Int → Int → Int
axiom step_skip : Int → Int → Int
axiom user_axiom_0 : (∀ G_ n_ : Int, ((is_valid_pm G_ n_ 0 (empty_matching )) = 1))
axiom user_axiom_1 : (∀ G_ n_ M_ : Int, (((is_valid_pm G_ n_ n_ M_) = 1) → ((is_max_matching G_ n_ M_) = 1)))
axiom user_axiom_2 : (∀ G_ n_ k_ M_ : Int, (((0 ≤ k_) ∧ (k_ < n_) ∧ ((is_valid_pm G_ n_ k_ M_) = 1)) → ((is_valid_pm G_ n_ (k_ + 1) (step_glover G_ M_ k_)) = 1)))
axiom user_axiom_3 : (∀ G_ n_ k_ M_ : Int, (((0 ≤ k_) ∧ (k_ < n_) ∧ ((is_valid_pm G_ n_ k_ M_) = 1)) → ((is_valid_pm G_ n_ (k_ + 1) (step_greedy_first G_ M_ k_)) = 1)))
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc7_fallthrough
    (G B n M i : Int)
    (M' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : ((is_valid_pm G n i' M') = 1))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    ((is_max_matching G n M') = 1) := by
  have hi : i' = n := by omega
  rw [hi] at h_tau_0
  exact user_axiom_1 G n M' h_tau_0
end SynthLean.VerifyTmp
