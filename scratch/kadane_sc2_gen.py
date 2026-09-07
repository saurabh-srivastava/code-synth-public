"""Generate kadane sc2 (branch 0 inductive) .solved.lean files.

WRITTEN: 2026-05-17 — Phase X.S Lean-curation, sibling to
                       kadanegen.py (sc0).
USED FOR: lean/SynthLean/Y2Corpus/kadane_max_subarray/sc2_*
          for variants that ARE provable.

CONTEXT
-------
The 17 sc2 (branch 0 inductive — "extend current run") dumps
split into:
  - 11 PROVABLE: τ subsets where all goal conjuncts follow
    from the available hypotheses + user axioms.  This script
    handles them.
  - 6 INVALID: τ subsets that omit cur_ub but whose goal
    includes best_ub'.  best_ub' at q=i requires bounding
    sum_range A p (i+1) for any p ≤ i, which without cur_ub
    is unprovable.  Handled by kadane_sc2_inv_gen.py
    (.invalid.lean output).

PROOF DEPENDENCIES per goal conjunct:
  - i_le_n':  i' ≤ n.  From h_guard.1 (i < n).  Just omega.
  - cur_ub':  ∀p. 0 ≤ p ≤ i → sum_range A p (i+1) ≤ cur + A i.
    Uses h_tau cur_ub (for p ≤ i-1) + axiom 0 + h_guard.2
    (cur + A i ≥ A i ⟹ cur ≥ 0).  Most non-trivial proof.
  - witness': ∃p. 0 ≤ p ≤ i ∧ sum_range A p (i+1) = cur + A i.
    Inherits the witness from h_tau and steps via axiom 1.
  - best_ub': ∀p,q. 0 ≤ p ≤ q ≤ i → sum_range A p (q+1) ≤ best'.
    Case q ≤ i-1: from h_tau best_ub.  Case q = i: uses
    h_tau cur_ub + axiom 1.  Both feed into split_ifs on the
    best'=max(best, cur+A i) expression.
  - best_ge': best' ≥ cur'.  From the transition: best' =
    max(best, cur+A i) ≥ cur+A i = cur'.  Just split_ifs+omega.

OUTPUT
------
Wrote 11 sc2 .solved.lean.  All verify via `lake env lean`.

RE-RUNNING
----------
  cd /Users/saurabh/code/synthesizer
  .venv/bin/python scratch/kadane_sc2_gen.py

GENERALIZING
------------
The same dependency-analysis pattern (which goal conjunct
needs which hypothesis) is useful for any benchmark with
multi-conjunct goals + multiple τ atoms.  Identifying which
τ subsets are INVALID (need .invalid.lean) early prevents
wasted curation effort.
"""

from pathlib import Path

REPO = Path("/Users/saurabh/code/synthesizer")
CORPUS = REPO / "lean/SynthLean/Y2Corpus/kadane_max_subarray"

# Map: hash → (taus_in_order, goals_in_order).
# Hypothesis types (used both as h_tau and as goal):
#   "i_le_n":  i ≤ n
#   "cur_ub":  ∀p. 0 ≤ p ≤ i-1 → sum_range A p i ≤ cur
#   "witness": ∃p. 0 ≤ p ≤ i-1 ∧ sum_range A p i = cur
#   "best_ub": ∀p,q. 0 ≤ p ≤ q < i → sum_range A p (q+1) ≤ best
#   "best_ge": best ≥ cur

# 11 provable sc2 variants.
PROVABLE = {
    "0c3f25cc": dict(taus=["cur_ub", "best_ub", "best_ge"],
                     goals=["cur_ub", "best_ub", "best_ge"]),
    "4fb76db8": dict(taus=["cur_ub", "witness", "best_ub", "best_ge"],
                     goals=["cur_ub", "witness", "best_ub", "best_ge"]),
    "50961080": dict(taus=["cur_ub", "best_ub"],
                     goals=["cur_ub", "best_ub"]),
    "6694120d": dict(taus=["i_le_n", "witness"],
                     goals=["i_le_n", "witness"]),
    "6f53454d": dict(taus=["cur_ub", "witness", "best_ub"],
                     goals=["cur_ub", "witness", "best_ub"]),
    "74f26c35": dict(taus=["cur_ub", "witness"],
                     goals=["cur_ub", "witness"]),
    "9474b198": dict(taus=["cur_ub", "best_ge"],
                     goals=["cur_ub", "best_ge"]),
    "b144c2aa": dict(taus=["witness", "best_ge"],
                     goals=["witness", "best_ge"]),
    "ce73417d": dict(taus=["cur_ub", "witness", "best_ge"],
                     goals=["cur_ub", "witness", "best_ge"]),
    "d08bce9c": dict(taus=["cur_ub"],
                     goals=["cur_ub"]),
    "dd97fe5d": dict(taus=["witness"],
                     goals=["witness"]),
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


# Each proof block returns the inner proof lines (already indented at "  · ").
# Indices into taus are dynamic; we generate index lookups.

def find_tau(taus: list[str], name: str) -> int | None:
    if name in taus:
        return taus.index(name)
    return None


def proof_block(goal: str, taus: list[str]) -> list[str]:
    """Return the proof lines for `goal` using the given tau ordering."""
    cur_ub_idx = find_tau(taus, "cur_ub")
    witness_idx = find_tau(taus, "witness")
    best_ub_idx = find_tau(taus, "best_ub")
    best_ge_idx = find_tau(taus, "best_ge")
    i_le_n_idx = find_tau(taus, "i_le_n")

    if goal == "i_le_n":
        # i' = i + 1 ≤ n from h_guard.1 (i < n).
        return ["obtain ⟨h_lt, _⟩ := h_guard", "omega"]
    if goal == "cur_ub":
        # ∀ p. 0 ≤ p ≤ i → sum_range A p (i+1) ≤ cur + A i.
        return [
            "obtain ⟨h_lt, h_cur_nn_guard⟩ := h_guard",
            "have h_cur_nn : cur ≥ 0 := by omega",
            "intro p hp",
            "obtain ⟨hp0, hp1⟩ := hp",
            "have h_step : sum_range A p (i + 1) = sum_range A p i + A i := by",
            "  exact user_axiom_1 A p i (by omega)",
            "by_cases hpi : p = i",
            "· subst hpi",
            "  rw [h_step]",
            "  have h_self : sum_range A p p = 0 := user_axiom_0 A p",
            "  rw [h_self]",
            "  omega",
            "· have hp_lt_i : p ≤ i - 1 := by omega",
            f"  have h_bound := h_tau_{cur_ub_idx} p ⟨hp0, hp_lt_i⟩",
            "  rw [h_step]",
            "  omega",
        ]
    if goal == "witness":
        # Use the witness p* from h_tau_witness.
        return [
            f"obtain ⟨p_star, h_p0, h_p1, h_sum⟩ := h_tau_{witness_idx}",
            "refine ⟨p_star, ?_, ?_, ?_⟩",
            "· exact h_p0",
            "· omega",
            "· have h_step : sum_range A p_star (i + 1) = sum_range A p_star i + A i := by",
            "    exact user_axiom_1 A p_star i (by omega)",
            "  rw [h_step, h_sum]",
        ]
    if goal == "best_ub":
        # ∀p,q. 0 ≤ p ≤ q < i+1 → sum_range A p (q+1) ≤ best'.
        # After subst_eqs, best' is replaced by the if-then-else;
        # work directly with that.
        return [
            "obtain ⟨h_lt, h_cur_nn_guard⟩ := h_guard",
            "have h_cur_nn : cur ≥ 0 := by omega",
            "intro p q hpq",
            "obtain ⟨hp0, hpq', hq⟩ := hpq",
            "by_cases hq_eq : q = i",
            "· subst hq_eq",
            "  -- Need sum_range A p (q+1) ≤ max(best, cur + A i).",
            "  have h_step : sum_range A p (q + 1) = sum_range A p q + A q := by",
            "    exact user_axiom_1 A p q (by omega)",
            "  by_cases hp_eq : p = q",
            "  · subst hp_eq",
            "    rw [h_step]",
            "    have h_self : sum_range A p p = 0 := user_axiom_0 A p",
            "    rw [h_self]",
            "    split_ifs <;> omega",
            "  · have hp_lt_q : p ≤ q - 1 := by omega",
            f"    have h_bound := h_tau_{cur_ub_idx} p ⟨hp0, hp_lt_q⟩",
            "    rw [h_step]",
            "    split_ifs <;> omega",
            "· have hq_lt_i : q < i := by omega",
            f"  have h_bound := h_tau_{best_ub_idx} p q ⟨hp0, hpq', hq_lt_i⟩",
            "  split_ifs <;> omega",
        ]
    if goal == "best_ge":
        # best' = max(best, cur + A i) ≥ cur + A i = cur'.
        return [
            "show (if best ≥ cur + A i then best else cur + A i) ≥ cur + A i",
            "split_ifs <;> omega",
        ]
    raise ValueError(f"unknown goal {goal}")


HEADER = """\
/-
kadane_max_subarray sc2 (branch 0: cur + A[i] ≥ A[i] — extend run)
inductive for τ subset {{{tau_desc}}}.

Transition: cur' = cur + A[i], best' = max(best, cur + A[i]), i' = i + 1.
-/
import SynthLean.Basic
open SynthLean

axiom sum_range : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ p : Int, ((sum_range A p p) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ p q : Int, ((p ≤ q) → ((sum_range A p (q + 1)) = ((sum_range A p q) + (A q)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
"""


def emit_file(hashstr: str, taus: list[str], goals: list[str]) -> str:
    body = HEADER.format(tau_desc=", ".join(taus))
    body += "theorem sc2_fallthrough\n"
    body += "    (n best i cur : Int)\n"
    body += "    (A : Int → Int)\n"
    body += "    (best' i' cur' : Int)\n"
    body += "    (h_pre : (n ≥ 1))\n"
    for k, name in enumerate(taus):
        body += f"    (h_tau_{k} : {TAU_DECL[name]})\n"
    body += "    (h_guard : ((i < n) ∧ ((cur + (A i)) ≥ (A i))))\n"
    body += "    (h_trans_cur : cur' = (cur + (A i)))\n"
    body += "    (h_trans_best : best' = (if (best ≥ (cur + (A i))) then best else (cur + (A i))))\n"
    body += "    (h_trans_i : i' = (i + 1)) :\n"
    goal_str = " ∧ ".join(GOAL_DECL[g] for g in goals)
    body += f"    {goal_str} := by\n"
    body += "  subst_eqs\n"
    if len(goals) == 1:
        for ln in proof_block(goals[0], taus):
            body += f"  {ln}\n"
    else:
        holes = ", ".join("?_" for _ in goals)
        body += f"  refine ⟨{holes}⟩\n"
        for g in goals:
            block = proof_block(g, taus)
            if len(block) == 1:
                body += f"  · {block[0]}\n"
            else:
                body += f"  · {block[0]}\n"
                for ln in block[1:]:
                    body += f"    {ln}\n"
    body += "\nend SynthLean.VerifyTmp\n"
    return body


for h, v in PROVABLE.items():
    body = emit_file(h, v["taus"], v["goals"])
    (CORPUS / f"sc2_fallthrough_{h}.solved.lean").write_text(body)
    print(f"wrote sc2_fallthrough_{h}.solved.lean")
