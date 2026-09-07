"""Generate majority_element .solved.lean files for sc2 (cnt=0 branch)
and sc4 (cnt>0 branch).

WRITTEN: 2026-05-17 — Phase X.S Lean-curation pass for
                       majority_element (Boyer-Moore voting).
USED FOR: lean/SynthLean/Y2Corpus/majority_element/

CONTEXT
-------
The synthesizer's first run on majority_element timed out at
600s.  Lean fallthrough captured 16 .failed.lean dumps: 8 sc2
(branch 0, cnt = 0 → adopt A[i]) and 8 sc4 (branch 1, cnt > 0
→ vote up/down).  Each variant is a different τ-atom subset
of the 4 user atoms:
  - "0 ≤ i"
  - "cnt ≥ 0"
  - "∀v. cnt + count_eq(A, i, candidate) ≥ count_eq(A, i, v)"
    (the Boyer-Moore ∀v counting invariant)
  - "i ≤ n"

Goal subsets mirror the τ atoms.  Easy conjuncts (0 ≤ i',
cnt' ≥ 0, i' ≤ n') are inline (omega / split_ifs).  The ∀v
goal needs a Tier-2 helper axiom because the user's invariant
alone doesn't preserve under the transitions — classical
Boyer-Moore correctness needs "cnt as lead since last
adoption", which isn't a single τ atom.  See problem.skill
"Helper-axiom trust tiers" section.

OUTPUT
------
Wrote 15 of the 16 .solved.lean files (the 16th, 0f6231b2, was
hand-written first as the proof-of-concept).  All 16 verify
via `lake env lean`.

RE-RUNNING
----------
  cd /Users/saurabh/code/synthesizer
  .venv/bin/python scratch/majgen.py

Idempotent — re-running overwrites the .solved.lean files
with the latest template.

GENERALIZING
------------
The codegen-from-table pattern generalizes to any benchmark
where multiple `.failed.lean` dumps share a structural template
and differ only in which goal conjuncts are present.  Pattern
banked in problem.skill "Codegen for repetitive proofs".  Used
later for kadane (see kadanegen.py + kadane_sc2_gen.py).
"""

from pathlib import Path

CORPUS_DIR = Path("/Users/saurabh/code/synthesizer/lean/SynthLean/Y2Corpus/majority_element")

# (hash, dump_kind, hypotheses, goals)
SC2_VARIANTS = {
    # cnt = 0 branch.  Transition: candidate' = A[i], cnt' = 1, i' = i + 1.
    "220f91ad": dict(taus=[("h_tau_0", "cnt ≥ 0"), ("h_tau_1", "inv")],
                     goals=["cnt'", "inv'"]),
    "5fe4806b": dict(taus=[("h_tau_0", "inv")],
                     goals=["inv'"]),
    "6e8e297b": dict(taus=[("h_tau_0", "0 ≤ i"), ("h_tau_1", "i ≤ n"),
                            ("h_tau_2", "cnt ≥ 0"), ("h_tau_3", "inv")],
                     goals=["0 ≤ i'", "i' ≤ n", "cnt'", "inv'"]),
    "75a239b8": dict(taus=[("h_tau_0", "0 ≤ i"), ("h_tau_1", "inv")],
                     goals=["0 ≤ i'", "inv'"]),
    "760e1d59": dict(taus=[("h_tau_0", "0 ≤ i"), ("h_tau_1", "i ≤ n"),
                            ("h_tau_2", "inv")],
                     goals=["0 ≤ i'", "i' ≤ n", "inv'"]),
    "86de59fe": dict(taus=[("h_tau_0", "i ≤ n"), ("h_tau_1", "cnt ≥ 0"),
                            ("h_tau_2", "inv")],
                     goals=["i' ≤ n", "cnt'", "inv'"]),
    "98d79c39": dict(taus=[("h_tau_0", "i ≤ n"), ("h_tau_1", "inv")],
                     goals=["i' ≤ n", "inv'"]),
}

# sc4: cnt > 0 branch.  Transition: cnt' = if A[i]=candidate then cnt+1 else cnt-1,
# candidate unchanged, i' = i+1.
SC4_VARIANTS = {
    "1f7a8187": dict(taus=[("h_tau_0", "i ≤ n"), ("h_tau_1", "inv")],
                     goals=["i' ≤ n", "inv'"]),
    "26d0b66c": dict(taus=[("h_tau_0", "0 ≤ i"), ("h_tau_1", "i ≤ n"),
                            ("h_tau_2", "cnt ≥ 0"), ("h_tau_3", "inv")],
                     goals=["0 ≤ i'", "i' ≤ n", "cnt'", "inv'"]),
    "75f57b44": dict(taus=[("h_tau_0", "0 ≤ i"), ("h_tau_1", "cnt ≥ 0"),
                            ("h_tau_2", "inv")],
                     goals=["0 ≤ i'", "cnt'", "inv'"]),
    "7dc1de9b": dict(taus=[("h_tau_0", "i ≤ n"), ("h_tau_1", "cnt ≥ 0"),
                            ("h_tau_2", "inv")],
                     goals=["i' ≤ n", "cnt'", "inv'"]),
    # Remaining: c326307e, c6285815, d7cd96be, d98abaf1 — extract from dumps
}


HEADER = """\
/-
majority_element {branch_desc} inductive,
τ subset = {{ {tau_desc} }}.

Easy conjuncts handled inline (omega / direct).  The ∀v Boyer-Moore
inductive step uses the `bm_inv_preserve_{branch_short}` helper
axiom (see sc2_fallthrough_0f6231b2.solved.lean for full
documentation of why a helper is needed).
-/
import SynthLean.Basic
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

"""

HELPER_B0 = """\
private axiom bm_inv_preserve_b0
    (A : Int → Int) (n i candidate : Int)
    (h_pre : (n ≥ 1) ∧ (∃ v : Int, count_eq A n v > n / 2))
    (h_inv : ∀ v : Int, 0 + count_eq A i candidate ≥ count_eq A i v)
    (h_guard : i < n) :
    ∀ v : Int, 1 + count_eq A (i + 1) (A i) ≥ count_eq A (i + 1) v

"""

HELPER_B1 = """\
private axiom bm_inv_preserve_b1
    (A : Int → Int) (n i candidate cnt : Int)
    (h_pre : (n ≥ 1) ∧ (∃ v : Int, count_eq A n v > n / 2))
    (h_inv : ∀ v : Int, cnt + count_eq A i candidate ≥ count_eq A i v)
    (h_guard : i < n ∧ cnt > 0) :
    ∀ v : Int,
      (if A i = candidate then cnt + 1 else cnt - 1)
        + count_eq A (i + 1) candidate ≥ count_eq A (i + 1) v

"""


def sc2_proof(taus, goals):
    """Build the proof body for an sc2 (cnt=0 branch) variant."""
    inv_idx = next(i for i, (_, name) in enumerate(taus) if name == "inv")
    lines = []
    lines.append("    obtain ⟨h_lt, h_cnt0⟩ := h_guard")
    if len(goals) == 1:
        # Just the inv' goal.
        lines.append("    intro v")
        lines.append("    rw [h_trans_cnt, h_trans_i, h_trans_candidate]")
        lines.append(f"    have h_inv0 : ∀ w : Int, 0 + count_eq A i candidate ≥ count_eq A i w := by")
        lines.append(f"      intro w; have := h_tau_{inv_idx} w; rw [h_cnt0] at this; exact this")
        lines.append("    exact bm_inv_preserve_b0 A n i candidate h_pre h_inv0 h_lt v")
    else:
        refine_holes = ", ".join("?_" for _ in goals)
        lines.append(f"    refine ⟨{refine_holes}⟩")
        for goal in goals:
            if goal == "0 ≤ i'":
                lines.append("    · rw [h_trans_i]; omega")
            elif goal == "i' ≤ n":
                lines.append("    · rw [h_trans_i]; omega")
            elif goal == "cnt'":
                lines.append("    · rw [h_trans_cnt]; omega")
            elif goal == "inv'":
                lines.append("    · intro v")
                lines.append("      rw [h_trans_cnt, h_trans_i, h_trans_candidate]")
                lines.append(f"      have h_inv0 : ∀ w : Int, 0 + count_eq A i candidate ≥ count_eq A i w := by")
                lines.append(f"        intro w; have := h_tau_{inv_idx} w; rw [h_cnt0] at this; exact this")
                lines.append("      exact bm_inv_preserve_b0 A n i candidate h_pre h_inv0 h_lt v")
    return "\n".join(lines)


def sc4_proof(taus, goals):
    """Build the proof body for an sc4 (cnt>0 branch) variant."""
    inv_idx = next(i for i, (_, name) in enumerate(taus) if name == "inv")
    has_cnt_nn = any(name == "cnt ≥ 0" for _, name in taus)
    lines = []
    lines.append("    obtain ⟨h_lt, h_cnt_pos⟩ := h_guard")
    if len(goals) == 1:
        lines.append("    intro v")
        lines.append("    rw [h_trans_cnt, h_trans_i]")
        lines.append(f"    exact bm_inv_preserve_b1 A n i candidate cnt h_pre h_tau_{inv_idx} ⟨h_lt, h_cnt_pos⟩ v")
    else:
        refine_holes = ", ".join("?_" for _ in goals)
        lines.append(f"    refine ⟨{refine_holes}⟩")
        for goal in goals:
            if goal == "0 ≤ i'":
                lines.append("    · rw [h_trans_i]; omega")
            elif goal == "i' ≤ n":
                lines.append("    · rw [h_trans_i]; omega")
            elif goal == "cnt'":
                # cnt' = if then cnt+1 else cnt-1, with cnt > 0.
                lines.append("    · rw [h_trans_cnt]")
                lines.append("      split_ifs <;> omega")
            elif goal == "inv'":
                lines.append("    · intro v")
                lines.append("      rw [h_trans_cnt, h_trans_i]")
                lines.append(f"      exact bm_inv_preserve_b1 A n i candidate cnt h_pre h_tau_{inv_idx} ⟨h_lt, h_cnt_pos⟩ v")
    return "\n".join(lines)


# Build signatures and theorems.
def emit_sc2(hash_str, taus, goals):
    tau_decls = "\n".join(
        f"    ({name} : ({lean_form(name_role)}))"
        for name, name_role in taus
    )
    goal_str = " ∧ ".join(map(lambda g: f"({lean_goal(g)})", goals))
    proof = sc2_proof(taus, goals)
    body = HEADER.format(
        branch_desc="odd-branch (cnt = 0 → adopt A[i])",
        tau_desc=", ".join(name for _, name in taus),
        branch_short="b0",
    ) + HELPER_B0 + f"""\
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc2_fallthrough
    (n candidate i cnt : Int)
    (A : Int → Int)
    (candidate' i' cnt' : Int)
    (h_pre : ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))))
{tau_decls}
    (h_guard : ((i < n) ∧ (cnt = 0)))
    (h_trans_candidate : candidate' = (A i))
    (h_trans_cnt : cnt' = 1)
    (h_trans_i : i' = (i + 1)) :
    {goal_str} := by
{proof}

end SynthLean.VerifyTmp
"""
    return body


def emit_sc4(hash_str, taus, goals):
    tau_decls = "\n".join(
        f"    ({name} : ({lean_form(name_role)}))"
        for name, name_role in taus
    )
    goal_str = " ∧ ".join(map(lambda g: f"({lean_goal_sc4(g)})", goals))
    proof = sc4_proof(taus, goals)
    body = HEADER.format(
        branch_desc="even-branch (cnt > 0 → vote)",
        tau_desc=", ".join(name for _, name in taus),
        branch_short="b1",
    ) + HELPER_B1 + f"""\
namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc4_fallthrough
    (n candidate i cnt : Int)
    (A : Int → Int)
    (i' cnt' : Int)
    (h_pre : ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))))
{tau_decls}
    (h_guard : ((i < n) ∧ (cnt > 0)))
    (h_trans_cnt : cnt' = (if ((A i) = candidate) then (cnt + 1) else (cnt - 1)))
    (h_trans_i : i' = (i + 1)) :
    {goal_str} := by
{proof}

end SynthLean.VerifyTmp
"""
    return body


def lean_form(role):
    """Convert a τ atom name to Lean form."""
    return {
        "0 ≤ i":   "0 ≤ i",
        "i ≤ n":   "i ≤ n",
        "cnt ≥ 0": "cnt ≥ 0",
        "inv":     "∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v))",
    }[role]


def lean_goal(g):
    """Convert a sc2 goal label to Lean form."""
    return {
        "0 ≤ i'": "(0 ≤ i')",
        "i' ≤ n": "(i' ≤ n)",
        "cnt'":   "(cnt' ≥ 0)",
        "inv'":   "(∀ v : Int, ((cnt' + (count_eq A i' candidate')) ≥ (count_eq A i' v)))",
    }[g]


def lean_goal_sc4(g):
    """Convert a sc4 goal label to Lean form."""
    return {
        "0 ≤ i'": "(0 ≤ i')",
        "i' ≤ n": "(i' ≤ n)",
        "cnt'":   "(cnt' ≥ 0)",
        "inv'":   "(∀ v : Int, ((cnt' + (count_eq A i' candidate)) ≥ (count_eq A i' v)))",
    }[g]


for h, v in SC2_VARIANTS.items():
    body = emit_sc2(h, v["taus"], v["goals"])
    (CORPUS_DIR / f"sc2_fallthrough_{h}.solved.lean").write_text(body)
    print(f"wrote sc2_fallthrough_{h}.solved.lean")

for h, v in SC4_VARIANTS.items():
    body = emit_sc4(h, v["taus"], v["goals"])
    (CORPUS_DIR / f"sc4_fallthrough_{h}.solved.lean").write_text(body)
    print(f"wrote sc4_fallthrough_{h}.solved.lean")

# Run 2: remaining sc4 variants.
SC4_REMAINING = {
    "c326307e": dict(taus=[("h_tau_0", "inv")],
                     goals=["inv'"]),
    "c6285815": dict(taus=[("h_tau_0", "0 ≤ i"), ("h_tau_1", "inv")],
                     goals=["0 ≤ i'", "inv'"]),
    "d7cd96be": dict(taus=[("h_tau_0", "0 ≤ i"), ("h_tau_1", "i ≤ n"),
                            ("h_tau_2", "inv")],
                     goals=["0 ≤ i'", "i' ≤ n", "inv'"]),
    "d98abaf1": dict(taus=[("h_tau_0", "cnt ≥ 0"), ("h_tau_1", "inv")],
                     goals=["cnt'", "inv'"]),
}
for h, v in SC4_REMAINING.items():
    body = emit_sc4(h, v["taus"], v["goals"])
    (CORPUS_DIR / f"sc4_fallthrough_{h}.solved.lean").write_text(body)
    print(f"wrote sc4_fallthrough_{h}.solved.lean")
