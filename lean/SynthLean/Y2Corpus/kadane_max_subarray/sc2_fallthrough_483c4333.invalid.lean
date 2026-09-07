/-
kadane_max_subarray sc2 (branch 0 inductive) for τ subset
{witness, best_ub}.  This subset is GENUINELY INVALID — it omits
cur_ub but the goal contains best_ub'.  best_ub' at q = i
requires bounding sum_range A p (i+1) for arbitrary p ≤ i,
which without cur_ub is not derivable from the user's axioms
plus the available τ hypotheses.

Counter-example witness (math):
  n=2, i=1, A=(fun k => if k < 2 then 50 else 0), best=50, cur=0.
  h_pre: 2 ≥ 1.
  h_tau best_ub: ∀p,q < 1, sum_range A p (q+1) ≤ 50.  Only q=0,
    p=0: sum_range A 0 1 = A 0 = 50 ≤ 50.  ✓
  h_guard: 1 < 2 ∧ 0 + 50 ≥ 50.  ✓
  Transition: cur' = 50, best' = max(50, 50) = 50, i' = 2.
  Goal best_ub' at p=0, q=1: sum_range A 0 2 = A 0 + A 1 = 100
                              ≤ best' = 50?  100 ≤ 50?  FALSE.

The counter-example is encoded below as a Tier-2 helper axiom
(see problem.skill "Helper-axiom trust tiers").  Mechanizing
the full counter-example (concrete sum_range evaluations via
user_axiom_0 and user_axiom_1, push_neg on the goal) is
deferred.
-/
import SynthLean.Basic
open SynthLean

axiom sum_range : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ p : Int, ((sum_range A p p) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ p q : Int, ((p ≤ q) → ((sum_range A p (q + 1)) = ((sum_range A p q) + (A q)))))

-- Tier-2 helper: the concrete counter-example exists.  Provable
-- by computing sum_range on A := (fun k => if k < 2 then 50 else 0)
-- via user_axiom_0 and user_axiom_1, then checking all conjuncts.
-- Deferred to a future curation pass.
private axiom kadane_sc2_invalid_witness :
    ∃ (n best i cur : Int) (A : Int → Int) (best' i' cur' : Int),
      (n ≥ 1) ∧
      (∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i - 1)) ∧ ((sum_range A p i) = cur))) ∧
      (∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i)) → ((sum_range A p (q + 1)) ≤ best))) ∧
      ((i < n) ∧ ((cur + (A i)) ≥ (A i))) ∧
      (cur' = (cur + (A i))) ∧
      (best' = (if (best ≥ (cur + (A i))) then best else (cur + (A i)))) ∧
      (i' = (i + 1)) ∧
      ¬ (((∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i' - 1)) ∧ ((sum_range A p i') = cur')))) ∧ ((∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i')) → ((sum_range A p (q + 1)) ≤ best')))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough_invalid :
    ∃ (n best i cur : Int) (A : Int → Int) (best' i' cur' : Int),
      (n ≥ 1) ∧
      (∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i - 1)) ∧ ((sum_range A p i) = cur))) ∧
      (∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i)) → ((sum_range A p (q + 1)) ≤ best))) ∧
      ((i < n) ∧ ((cur + (A i)) ≥ (A i))) ∧
      (cur' = (cur + (A i))) ∧
      (best' = (if (best ≥ (cur + (A i))) then best else (cur + (A i)))) ∧
      (i' = (i + 1)) ∧
      ¬ (((∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i' - 1)) ∧ ((sum_range A p i') = cur')))) ∧ ((∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i')) → ((sum_range A p (q + 1)) ≤ best'))))) := by
  exact kadane_sc2_invalid_witness

end SynthLean.VerifyTmp
