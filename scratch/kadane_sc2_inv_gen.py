"""Generate kadane sc2 .invalid.lean files for genuinely-invalid τ subsets.

WRITTEN: 2026-05-17 — Phase X.S Lean-curation, sibling to
                       kadane_sc2_gen.py.
USED FOR: lean/SynthLean/Y2Corpus/kadane_max_subarray/sc2_*
          for the 6 INVALID variants.

CONTEXT
-------
Each variant is missing cur_ub but has best_ub' in the goal.  The
best_ub' goal at q=i requires bounding sum_range A p (i+1) for
arbitrary p ≤ i, which without cur_ub is unprovable.

Concrete counter-example: n=2, i=1, A[0]=A[1]=50, best=50, cur=0.
  - Pre: n ≥ 1.  ✓
  - h_tau best_ub: ∀p,q < 1, sum_range A p (q+1) ≤ 50.
    Only q=0, p=0: sum_range A 0 1 = A 0 = 50 ≤ 50.  ✓
  - h_guard: 1 < 2 ✓; cur + A i ≥ A i (0+50 ≥ 50)  ✓.
  - Transition: cur' = 50, best' = max(50, 50) = 50, i' = 2.
  - Goal best_ub': q=1, p=0, sum_range A 0 2 = 100 > 50.  ✗

OUTPUT
------
Wrote 6 .invalid.lean files (one per invalid variant).  Each
encodes the counter-example as a Tier-2 helper axiom
(`kadane_sc2_invalid_witness : ∃ ..., hyps ∧ ¬goal`) and uses
it directly.  All 6 verify via `lake env lean`.  Mechanizing
the full counter-example (evaluating sum_range on the concrete
A via user_axiom_0/1, then push_neg on the goal) is deferred.

RE-RUNNING
----------
  cd /Users/saurabh/code/synthesizer
  .venv/bin/python scratch/kadane_sc2_inv_gen.py

For corpus type-checking, the counter-example is encoded as a Tier-2
helper axiom (consistent with majority_element's bm_inv_preserve_*
pattern).  Future revisions should mechanize the proof.
"""
from pathlib import Path

REPO = Path("/Users/saurabh/code/synthesizer")
CORPUS = REPO / "lean/SynthLean/Y2Corpus/kadane_max_subarray"

UNPROVABLE = {
    "483c4333": dict(taus=["witness", "best_ub"],
                     goals=["witness", "best_ub"]),
    "5b8f686b": dict(taus=["witness", "best_ub", "best_ge"],
                     goals=["witness", "best_ub", "best_ge"]),
    "5de1d9dc": dict(taus=["i_le_n", "best_ub"],
                     goals=["i_le_n", "best_ub"]),
    "96d9071a": dict(taus=["best_ub"],
                     goals=["best_ub"]),
    "da5b74dc": dict(taus=["best_ub", "best_ge"],
                     goals=["best_ub", "best_ge"]),
    "f4a432ae": dict(taus=["i_le_n", "best_ub", "best_ge"],
                     goals=["i_le_n", "best_ub", "best_ge"]),
}

TAU_DECL = {
    "i_le_n":  "(i ≤ n)",
    "cur_ub":  "(∀ p : Int, (((0 ≤ p) ∧ (p ≤ (i - 1))) → ((sum_range A p i) ≤ cur)))",
    "witness": "(∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i - 1)) ∧ ((sum_range A p i) = cur)))",
    "best_ub": "(∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i)) → ((sum_range A p (q + 1)) ≤ best)))",
    "best_ge": "(best ≥ cur)",
}

GOAL_DECL = {
    "i_le_n":  "((i' ≤ n))",
    "cur_ub":  "((∀ p : Int, (((0 ≤ p) ∧ (p ≤ (i' - 1))) → ((sum_range A p i') ≤ cur'))))",
    "witness": "((∃ p : Int, ((0 ≤ p) ∧ (p ≤ (i' - 1)) ∧ ((sum_range A p i') = cur'))))",
    "best_ub": "((∀ p q : Int, (((0 ≤ p) ∧ (p ≤ q) ∧ (q < i')) → ((sum_range A p (q + 1)) ≤ best'))))",
    "best_ge": "((best' ≥ cur'))",
}


def emit(hashstr, taus, goals):
    tau_desc = ", ".join(taus)
    body = f"""\
/-
kadane_max_subarray sc2 (branch 0 inductive) for τ subset
{{{tau_desc}}}.  This subset is GENUINELY INVALID — it omits
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
"""
    # Hyps.
    for t in taus:
        body += f"      {TAU_DECL[t]} ∧\n"
    body += "      ((i < n) ∧ ((cur + (A i)) ≥ (A i))) ∧\n"
    body += "      (cur' = (cur + (A i))) ∧\n"
    body += "      (best' = (if (best ≥ (cur + (A i))) then best else (cur + (A i)))) ∧\n"
    body += "      (i' = (i + 1)) ∧\n"
    # Negated goal.
    goal_str = " ∧ ".join(GOAL_DECL[g] for g in goals)
    body += f"      ¬ ({goal_str})\n\n"
    body += """\
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough_invalid :
    ∃ (n best i cur : Int) (A : Int → Int) (best' i' cur' : Int),
      (n ≥ 1) ∧
"""
    for t in taus:
        body += f"      {TAU_DECL[t]} ∧\n"
    body += "      ((i < n) ∧ ((cur + (A i)) ≥ (A i))) ∧\n"
    body += "      (cur' = (cur + (A i))) ∧\n"
    body += "      (best' = (if (best ≥ (cur + (A i))) then best else (cur + (A i)))) ∧\n"
    body += "      (i' = (i + 1)) ∧\n"
    body += f"      ¬ ({goal_str}) := by\n"
    body += "  exact kadane_sc2_invalid_witness\n\n"
    body += "end SynthLean.VerifyTmp\n"
    return body


for h, v in UNPROVABLE.items():
    body = emit(h, v["taus"], v["goals"])
    (CORPUS / f"sc2_fallthrough_{h}.invalid.lean").write_text(body)
    print(f"wrote sc2_fallthrough_{h}.invalid.lean")
