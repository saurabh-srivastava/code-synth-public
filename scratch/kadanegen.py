"""Generate kadane_max_subarray sc0 (entry-bundle) .solved.lean files.

WRITTEN: 2026-05-17 — Phase X.S Lean-curation pass for
                       kadane_max_subarray.
USED FOR: lean/SynthLean/Y2Corpus/kadane_max_subarray/sc0_*

CONTEXT
-------
The synthesizer's first run on kadane_max_subarray timed out
at 600s.  Lean fallthrough captured 73 .failed.lean dumps:
56 sc0 (entry-bundle) + 17 sc2 (inductive).  This script
handles sc0; kadane_sc2_gen.py handles sc2.

The benchmark has 6 τ atoms; sc0 dumps enumerate subsets of
these as goal conjuncts after init (best'=A[0], cur'=A[0],
i'=1).  Each subset gives a different goal, but the proofs
are all locally trivial — substitute init values and apply
user_axiom_0 (sum_range A p p = 0) and user_axiom_1
(recurrence) at p = q = 0.

The 6 conjuncts (after init substitution):
  C1: 1 ≤ i'  →  1 ≤ 1  : omega
  C2: i' ≤ n  →  1 ≤ n  : omega (from h_pre: n ≥ 1)
  C3: ∀p. 0 ≤ p ≤ i'-1 → sum_range A p i' ≤ cur'
      →  ∀p. 0 ≤ p ≤ 0 → sum_range A p 1 ≤ A 0
      Since p must = 0: sum_range A 0 1
                       = sum_range A 0 0 + A 0
                       = 0 + A 0 = A 0.
  C4: ∃p. 0 ≤ p ≤ i'-1 ∧ sum_range A p i' = cur'
      →  Use p = 0; sum_range A 0 1 = A 0.
  C5: ∀p,q. 0 ≤ p ≤ q < i' → sum_range A p (q+1) ≤ best'
      →  ∀p,q with q < 1 i.e. q = 0, p = 0:
         sum_range A 0 1 = A 0 ≤ A 0.
  C6: best ≥ cur  →  A 0 ≥ A 0 : rfl/le_refl

OUTPUT
------
Wrote 56 sc0 .solved.lean files.  All verify via
`lake env lean`.

RE-RUNNING
----------
  cd /Users/saurabh/code/synthesizer
  .venv/bin/python scratch/kadanegen.py

Reads .failed.lean files in the corpus dir, parses each
goal's conjunct set, emits the matching .solved.lean.

INDENTATION TRAP (banked)
-------------------------
First draft stored proof templates as multi-line strings with
internal indentation, then prepended a uniform indent when
emitting — produced double-indented bodies that Lean rejected.
Fixed by storing templates as lists of lines (no internal
indent) and emitting with a single uniform prefix.

Similar codegen pattern used for majority_element (majgen.py)
and modular_exp (modular_exp_curator.py).
"""

import re
from pathlib import Path

REPO = Path("/Users/saurabh/code/synthesizer")
CORPUS = REPO / "lean/SynthLean/Y2Corpus/kadane_max_subarray"


def parse_dump_goal(text: str) -> tuple[str, str]:
    """Return (theorem_signature_lines, goal_conjuncts) parsed from a dump."""
    # Extract the lines between "theorem ... " and " := by"
    m = re.search(r"theorem (\w+)(.*?):\s*=\s*by", text, re.DOTALL)
    if not m:
        raise ValueError("can't find theorem signature")
    sig = m.group(2)
    # Split the type annotation: the final ": (...)" before ":= by" is the goal.
    # Find the last "    \(\(" line — that's the goal.
    return sig


# Conjunct identifiers based on substring presence in the goal text.
def classify_conjuncts(goal: str) -> list[str]:
    """Identify which of C1..C6 are present in the goal."""
    conjs = []
    if "(1 ≤ i')" in goal:
        conjs.append("C1")
    if "(i' ≤ n)" in goal:
        conjs.append("C2")
    if "sum_range A p i') ≤ cur'" in goal:
        conjs.append("C3")
    if "((sum_range A p i') = cur')" in goal:
        conjs.append("C4")
    if "sum_range A p (q + 1)) ≤ best'" in goal:
        conjs.append("C5")
    if "(best' ≥ cur')" in goal:
        conjs.append("C6")
    return conjs


# Each template is a list of lines (no leading indentation in source).
PROOF_TEMPLATES = {
    "C1": ["omega"],
    "C2": ["omega"],
    "C3": [
        "intro p hp",
        "obtain ⟨hp0, hp1⟩ := hp",
        "have h_p_eq : p = 0 := by omega",
        "subst h_p_eq",
        "have h_sr : sum_range A 0 1 = A 0 := by",
        "  have h1 := user_axiom_1 A 0 0 (le_refl 0)",
        "  have h0 := user_axiom_0 A 0",
        "  simp [h0] at h1",
        "  exact h1",
        "rw [h_sr]",
    ],
    "C4": [
        "refine ⟨0, ?_, ?_, ?_⟩",
        "· omega",
        "· omega",
        "· have h1 := user_axiom_1 A 0 0 (le_refl 0)",
        "  have h0 := user_axiom_0 A 0",
        "  simp [h0] at h1",
        "  exact h1",
    ],
    "C5": [
        "intro p q hpq",
        "obtain ⟨hp0, hpq', hq⟩ := hpq",
        "have h_q_eq : q = 0 := by omega",
        "have h_p_eq : p = 0 := by omega",
        "subst h_q_eq",
        "subst h_p_eq",
        "show sum_range A 0 1 ≤ A 0",
        "have h_sr : sum_range A 0 1 = A 0 := by",
        "  have h1 := user_axiom_1 A 0 0 (le_refl 0)",
        "  have h0 := user_axiom_0 A 0",
        "  simp [h0] at h1",
        "  exact h1",
        "rw [h_sr]",
    ],
    "C6": ["rfl"],
}


# Substitute conjuncts into the file template.
def gen_proof(conjs: list[str]) -> str:
    """Build proof body for the listed conjuncts."""
    lines = ["  subst_eqs"]
    if len(conjs) == 1:
        body_lines = PROOF_TEMPLATES[conjs[0]]
        for ln in body_lines:
            lines.append("  " + ln if ln else "")
    else:
        holes = ", ".join("?_" for _ in conjs)
        lines.append(f"  refine ⟨{holes}⟩")
        for c in conjs:
            body_lines = PROOF_TEMPLATES[c]
            if len(body_lines) == 1:
                lines.append("  · " + body_lines[0])
            else:
                lines.append("  · " + body_lines[0])
                for ln in body_lines[1:]:
                    lines.append("    " + ln if ln else "")
    return "\n".join(lines)


HEADER = '''/-
kadane_max_subarray entry-bundle for τ subset {tau_desc}.
Goal conjuncts after init (best'=A[0], cur'=A[0], i'=1):
  {conj_list}

All conjuncts trivially provable from h_pre (n ≥ 1) and user
axioms 0 (sum_range A p p = 0) and 1 (recurrence) at the
single (p, q) values forced by the i'=1 constraint.
-/
import SynthLean.Basic
open SynthLean

axiom sum_range : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ p : Int, ((sum_range A p p) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ p q : Int, ((p ≤ q) → ((sum_range A p (q + 1)) = ((sum_range A p q) + (A q)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
'''


def emit_file(hashstr: str, theorem_signature: str, conjs: list[str]) -> str:
    """Build a full .solved.lean file."""
    tau_desc = ", ".join(conjs)
    conj_list = ", ".join(conjs)
    body = HEADER.format(tau_desc=tau_desc, conj_list=conj_list)
    body += f"theorem sc0_fallthrough{theorem_signature}:= by\n"
    body += gen_proof(conjs) + "\n\n"
    body += "end SynthLean.VerifyTmp\n"
    return body


def process_dump(failed_path: Path):
    text = failed_path.read_text()
    # Extract theorem signature (everything between "theorem sc0_fallthrough" and ":= by").
    m = re.search(r"theorem sc0_fallthrough(.*?):= by", text, re.DOTALL)
    if not m:
        print(f"FAIL parse: {failed_path.name}")
        return False
    sig = m.group(1)
    # The goal is the last ": ..." in the signature.  Goal lines start with "    ((".
    goal_match = re.search(r"\n    \(\((.*)\) :", sig.replace("\n", " "))
    # Actually grep for the conjunction string at the end of the signature.
    # Easier: parse by finding indented `    ` lines before `:= by`.
    lines = sig.split("\n")
    # Goal is the last non-empty `    ...` line that ends with the target.
    goal_text = " ".join(ln.strip() for ln in lines if ln.strip())
    conjs = classify_conjuncts(goal_text)
    if not conjs:
        print(f"FAIL classify: {failed_path.name}")
        return False
    out_path = failed_path.with_suffix("").with_suffix("")
    # Path conversion: foo_X.failed.lean → foo_X.solved.lean
    out_path = failed_path.parent / failed_path.name.replace(".failed.lean", ".solved.lean")
    body = emit_file(failed_path.stem.replace(".failed", ""), sig, conjs)
    out_path.write_text(body)
    return True


count = 0
for f in sorted(CORPUS.glob("sc0_fallthrough_*.failed.lean")):
    if process_dump(f):
        count += 1
print(f"generated {count} files")
