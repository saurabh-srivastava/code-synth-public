/-
sc7 post-bundle for l16_glover_verify, chosen τ = {is_valid_pm, 0≤i, i≤n}.

After ¬g (i.e., n ≤ i') and h_tau_2 (i' ≤ n), we have i' = n.
Substitute into h_tau_0 to get is_valid_pm G n n M' = 1, then
apply user_axiom_2 to derive is_max_matching G n M' = 1.
-/
import SynthLean.Core
open SynthLean

axiom is_valid_pm : Int → Int → Int → Int → Int
axiom is_max_matching : Int → Int → Int → Int
axiom empty_matching : Int
axiom process_endpoint : Int → Int → Int
axiom user_axiom_0 : (∀ G_ n_ : Int, ((is_valid_pm G_ n_ 0 (empty_matching )) = 1))
axiom user_axiom_1 : (∀ G_ n_ k_ M_ : Int, (((0 ≤ k_) ∧ (k_ < n_) ∧ ((is_valid_pm G_ n_ k_ M_) = 1)) → ((is_valid_pm G_ n_ (k_ + 1) (process_endpoint M_ k_)) = 1)))
axiom user_axiom_2 : (∀ G_ n_ M_ : Int, (((is_valid_pm G_ n_ n_ M_) = 1) → ((is_max_matching G_ n_ M_) = 1)))
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc7_fallthrough
    (G n M i : Int)
    (M' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : ((is_valid_pm G n i' M') = 1))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n))) :
    ((is_max_matching G n M') = 1) := by
  have hi : i' = n := by omega
  rw [hi] at h_tau_0
  exact user_axiom_2 G n M' h_tau_0
end SynthLean.VerifyTmp
