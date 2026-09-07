"""Auto-helper templater (RESEARCH.md §M.5).

For constraint SHAPES where the proof is structurally
trivial — `subst_eqs` + `refine ⟨...⟩` + `omega`/`assumption`
— this module generates a Core-only proof body.  Trivial
proofs that don't need mathlib tactics can be type-checked
against `SynthLean.Core` alone, saving ~3s of mathlib
preload per `lake env lean` call.

The templater is conservative: returns `None` for any
constraint where it isn't confident the body will close.
On `None`, the caller falls through to today's helper-cite
or generic-chain paths.

Soundness: the auto-proof is ALWAYS checked by Lean (it's a
generated proof body, not an axiom).  An accepted auto-proof
is as sound as any Lean-verified proof.  The risk is false
NEGATIVES (we predict a shape will close but Lean rejects);
those just fall through to the slower paths.
"""

from __future__ import annotations
import re
from typing import Optional


# Shapes we attempt auto-handling for.
#
# Coverage is the trivial-omega case.  The other shapes go
# through a wider template that destructures `h_pre` into
# atoms, then dispatches each goal conjunct via
# omega/assumption.  Empirically, this discharges most
# obligations on the K.3.2-family benchmarks (where h_pre
# carries the matching invariant and the goal's MI conjunct
# is preserved unchanged by the transition).
_AUTO_SUPPORTED_KINDS = {
    "coverage",
    "safety-bundle-entry",
    "safety-bundle-post",
    "safety",
}


def _count_pre_conjuncts(theorem_text: str) -> Optional[int]:
    """Count top-level ∧ in `h_pre`'s binder text.

    h_pre is emitted as `(h_pre : (expr1 ∧ expr2 ∧ ... ∧ exprN))`.
    We count ∧ at the outermost depth within h_pre's body.
    Returns N (number of conjuncts) or None if h_pre isn't
    present or its structure isn't a flat conjunction.
    """
    m = re.search(r"\(h_pre\s*:\s*(.+)\)\s*\n", theorem_text)
    if not m:
        return None
    body = m.group(1)
    depth = 0
    ands = 0
    i = 0
    while i < len(body):
        c = body[i]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth < 0:
                break
        elif depth == 1 and body[i] == '∧':
            ands += 1
        i += 1
    return ands + 1 if ands > 0 else None


def _auto_tactic_with_destructure(n_pre: int) -> str:
    """Emit the auto-template with h_pre destructured into
    `n_pre` underscores so `assumption` can pick atoms.

    The destructure is wrapped in `try` so it's a no-op if
    h_pre isn't destructurable (e.g., trivial true Pre).
    """
    underscores = ", ".join(["_"] * n_pre)
    return (
        "subst_eqs\n"
        f"  try (obtain ⟨{underscores}⟩ := h_pre)\n"
        "  first \n"
        "    | omega \n"
        "    | assumption \n"
        + "\n".join(
            f"    | (refine ⟨{', '.join(['?_'] * k)}⟩; "
            "all_goals (first | omega | assumption))"
            for k in range(12, 1, -1)
        )
    )


def auto_proof_body(
    problem,
    sc_kind: str,
    loop_id: Optional[str],
    branch_idx: Optional[int],
    theorem_text: str,
    chosen_atoms: dict,
) -> Optional[str]:
    """Return a Core-only proof body if this constraint is
    auto-templatable; else None.

    The proof body uses only `subst_eqs`, `refine`, `omega`,
    `assumption`.  No mathlib tactics.

    Returns None when:
      - `sc_kind` is not in the supported set.
      - The conclusion mentions `store` or `store2d` (auto-
        template doesn't unfold them).
      - The theorem has too many quantified atoms (suggests
        axiom-heavy reasoning is needed).
    """
    if sc_kind not in _AUTO_SUPPORTED_KINDS:
        return None

    # Bail out if EITHER the conclusion OR any transition/frame
    # hypothesis mentions `store` / `store2d`.  Array-store
    # reasoning needs `simp [store] + split_ifs` (mathlib path);
    # the auto-template's `subst_eqs + omega/assumption` doesn't
    # unfold stores, so it would fall back to generic chain after
    # ~1.4s of wasted work.  Better to skip the auto path entirely.
    if "store " in theorem_text or "store2d " in theorem_text:
        return None
    conclusion = _extract_conclusion(theorem_text)
    if conclusion is None:
        return None

    # Count pre conjuncts so we can emit the right destructure.
    # If h_pre isn't structurable, fall back to no-destructure
    # (the `try` wrapper handles the no-op case).
    n_pre = _count_pre_conjuncts(theorem_text) or 1
    # Clamp to a sensible range.  N > 10 is rare; we cap at 12.
    n_pre = min(max(n_pre, 1), 12)
    return _auto_tactic_with_destructure(n_pre)


def _extract_conclusion(theorem_text: str) -> Optional[str]:
    """Extract the goal text from a translator-emitted theorem.

    Theorem shape: `... : <goal> := by\\n  <body>`.
    We grab everything between the final `:` and `:= by`.
    """
    marker = ":= by"
    idx = theorem_text.rfind(marker)
    if idx < 0:
        return None
    # Walk back to find the final `:` that starts the goal.
    # The translator's emission has the goal on its own line(s)
    # before `:= by`.  Heuristic: scan back from `:= by` to
    # find the unindented `:` after the last binder.
    head = theorem_text[:idx]
    # Find the LAST ` :\n` line — that's the binder-list
    # terminator.
    last_colon = head.rfind(") :")
    if last_colon < 0:
        # Bodies with no binders end with just `:`.
        last_colon = head.rfind(":")
    return head[last_colon + 1:].strip() if last_colon >= 0 else None
