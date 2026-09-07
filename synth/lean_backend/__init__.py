"""synth.lean_backend — Lean 4 proof backend (Ring 1).

Translates IR-level synthesis obligations (atom strings + chosen
solution) into Lean theorem text, shells out to `lake build` for
verification.  Sister to the SMT path in `synth.solver`.

Translation level: IR atom strings, NOT Z3 expressions.  Each chosen
atom becomes a named hypothesis in the emitted theorem so proofs can
refer to invariants by name — closer to a Hoare-style obligation than
to a flat SMT conjunction.  See `RESEARCH.LEAN.md` for scoping.

Ring 1 status:
  - Day 1 (DONE): `lean/` Lake project + smoke test.
  - Day 2 (in progress): `translate.theorem_for_ranking_lb` — first
    obligation kind covered, end-to-end via `lake build`.
  - Day 3+ (next): more obligation kinds, then grid_paths.
"""

from .translate import (
    theorem_for_ranking_lb,
    theorem_for_ranking_decrease,
    theorem_for_safety_inductive,
    emit_axiom_declarations,
    lean_expr,
)
from .verify import (
    Verdict,
    lean_available,
    verify_class_via_lean,
)

__all__ = [
    "theorem_for_ranking_lb",
    "theorem_for_ranking_decrease",
    "theorem_for_safety_inductive",
    "emit_axiom_declarations",
    "lean_expr",
    "Verdict",
    "lean_available",
    "verify_class_via_lean",
]
