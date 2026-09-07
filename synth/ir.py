"""IR — minimal dataclass AST for templates and problems.

The IR mirrors POPL'10's flowgraph grammar `T ::= SB | Loop(T) | T;T | Recur`.
Each hole-bearing node has an optional ID field that the `expand` pass
fills in.  Hole IDs are how `Problem.atoms` keys map back to template
positions.

Naming convention for hole IDs (filled by expand):

  - `tau@L0`, `phi@L0`, `g@L0`   — invariant / ranking / guard of loop L0
  - `s@B0`                       — single transition of SB block B0 (n=1)
  - `s@B0.k`                     — branch k of SB block B0 with n>1
  - `s_recur@R0`                 — recursive-call transition (Phase 3+)
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, Union


def _is_absolute_path(p: str) -> bool:
    """Cross-platform absolute-path check (avoids os import at module top)."""
    import os
    return os.path.isabs(p)


@dataclass
class Var:
    """A typed program variable.

    role is one of "input" | "output" | "local"; informational for now,
    used by the decoder to choose pretty-printing.
    """
    name: str
    type: str = "int"
    role: str = "local"


# ─────────────────────────────────────────────────────────────────────
# Template AST.
# ─────────────────────────────────────────────────────────────────────

@dataclass
class SB:
    """Acyclic block (◦) with `n` guarded transitions.

    Phase 1.A only supports n=1.  Multiple branches (n>1) will land in
    Phase 1.5 with proper guard atoms and `⋁ g_i ≡ true` enforcement.
    """
    n: int = 1
    block_id: Optional[str] = None        # filled by expand


@dataclass
class Loop:
    """Loop `*(T)` — body T plus inferred τ, ϕ, g."""
    body: "Template"
    loop_id: Optional[str] = None         # filled by expand


@dataclass
class Seq:
    """Sequence `T;T`."""
    left: "Template"
    right: "Template"


@dataclass
class Recur:
    """Recursive self-call `~`.  Phase 3+; raises in expand for now."""
    recur_id: Optional[str] = None


Template = Union[SB, Loop, Seq, Recur]


# >> overload for sequencing.  Attached after class definitions to break
# the forward-reference cycle.
def _rshift(self, other):
    return Seq(self, other)


for _cls in (SB, Loop, Seq, Recur):
    _cls.__rshift__ = _rshift


# ─────────────────────────────────────────────────────────────────────
# Problem container.
# ─────────────────────────────────────────────────────────────────────

@dataclass
class Problem:
    """A synthesis problem.

    `atoms` maps hole IDs (assigned during expansion — see naming
    convention in module docstring) to lists of candidate atoms:

      - predicate holes (`tau@*`, `g@*`)  : list[str], expression strings
      - numeric holes (`phi@*`)           : list[str], expression strings
      - transition holes (`s@*`)          : list of either:
          * dict[str, str]            — parallel assignment.  Each key is
            an output var name, each value is the RHS expression.  RHS
            is evaluated over the pre-state binding only.  Vars not in
            the dict are preserved (x' = x).
          * list[dict[str, str]]      — SSA / sequential assignment.
            Each entry is a single-key dict {var: rhs}; later entries
            may reference earlier LHS variables, picking up the
            freshly-assigned value.  Symbolically inlined at
            constraint-generation time.

    The first atom per hole is conventionally the expected solution in
    benchmarks; this is purely a convention and does not affect solving.
    """
    template: Template
    inputs: list[Var]
    outputs: list[Var]
    locals: list[Var] = field(default_factory=list)
    pre: str = "true"
    post: str = "true"
    # English-language spec — what a user (or LLM) would write as the
    # problem description before authoring the Problem object.
    # RESEARCH.md §D Phase X builds the (description, Problem) corpus
    # for the driver-LLM in Phase Y.  Empty when the benchmark
    # predates the corpus discipline; new benchmarks should populate
    # this as the user-facing spec (NOT implementer notes).
    description: str = ""
    atoms: dict[str, list] = field(default_factory=dict)
    # Phase 3.D: uninterpreted functions + axioms.
    #   uninterpreted: [(name, [arg_type, …], return_type), …]
    #       Argument and return types are the same strings as Var.type
    #       (e.g. "int", "bool", "int[]").
    #   axioms: list of expression strings, parsed and asserted as
    #       universally-true premises in the CEGIS verifier.
    uninterpreted: list[tuple[str, list[str], str]] = field(default_factory=list)
    axioms: list[str] = field(default_factory=list)
    max_solutions: int = 10
    solver_timeout_ms: int = 60_000
    # P1 — solution-count regression guard.  If set, the regression
    # suite compares `len(result.solutions)` against this value and
    # FAILs on mismatch.  Acts as a soundness oracle: a constraint
    # accidentally dropped from emission (Lessons #27 / #30) typically
    # widens the solution set without breaking the post, and the count
    # drift catches it.  None ⇒ no check (incremental rollout for new
    # benchmarks).
    expected_solutions: int | None = None
    # Phase X / Ring 2 — Lean dispatch regression guard.  If set, the
    # regression suite compares `result.lean_dispatch.valid` against
    # this value and FAILs on drift.  Catches cases where:
    #   - A tactic-chain change shifts Z3 vs Lean responsibility
    #     (`expected_lean_hits` goes up means more obligations are
    #     now Lean-verified, which is a win — update the expected
    #     value).
    #   - A translator regression starts breaking obligations Lean
    #     used to prove (count goes down — regression).
    # Default for Z3-decidable benchmarks: 0.  Axiom-heavy
    # benchmarks (fib, factorial, sum_array, array_product,
    # count_zeros) report Lean dispatch counts in the hundreds;
    # the expected here is informative, not strict (Z3
    # nondeterminism makes per-class hit counts non-portable).
    expected_lean_hits: int | None = None
    # Soundness policy.  `False` (default — sound mode): synthesis
    # only returns solutions whose obligations were genuinely
    # verified by Z3 or the Lean backend (cache + generic chain).
    # When neither can decide, `NoSolution` is returned rather than
    # emit unverified code.
    #
    # `True` is an OPT-IN DEVELOPMENT ESCAPE HATCH for authoring
    # new benchmarks: it lets you check structural synthesis BEFORE
    # curating `.solved.lean` / `.invalid.lean` companions.
    # The solver's lenient promotion path that this flag once gated
    # was excised — no committed benchmark needs it, and turning
    # this flag on now still routes UNKNOWN classes to
    # unknown_deferred → REJECT.  The flag remains for callers who
    # set it via `--potentially-unsound` CLI (currently a no-op
    # path but reserved for future development workflows).  See
    # `SOUNDNESS.md` for the full posture.
    #
    # No production benchmark should set `True`.  A grep check in
    # CI fails any commit that does.
    potentially_unsound: bool = False
    # Phase Y.2 corpus building: when set to a directory path, every
    # Lean fallthrough call that returns unknown/error/timeout dumps
    # its .lean source there for human review (or driver-LLM training
    # later).  Per `RESEARCH.md` §D, the operating model is NOT to
    # write Lean proofs upfront; instead, each benchmark's failed
    # obligations get a proof written reactively, and those
    # (obligation, proof) pairs train the Phase Y.2 driver-LLM.
    dump_lean_failures_dir: str | None = None
    # RESEARCH.md §H.2 — unsat-core-inspired fast path for BOTH-
    # position τ atoms.  PROTOTYPE BANKED as research finding;
    # NOT YET FUNCTIONAL.
    #
    # ⚠️  Setting this to True does NOTHING currently — the
    # corresponding fast-path block in solver.py is hard-disabled
    # (`_fast_path_enabled = False`).  See RESEARCH.md
    # §H.2.PROTOTYPE for the unsoundness findings on
    # BOTH-position distractor atoms that prevent enabling.  DO
    # NOT remove this field or the supporting infrastructure in
    # solver.py without reading those findings — they document
    # what a re-implementation has to handle.
    use_unsat_core_fast_path: bool = False
    # RESEARCH.md §H.2 — Tier-3-helper citation codegen.  When set,
    # the Lean verifier consults the registry before running the
    # generic tactic chain; matching obligations get a one-line
    # `exact <helper> <args>` proof body, type-checking in ~2s
    # instead of 30-60s.  See `synth/lean_backend/codegen.py` for
    # the contract.  None ⇒ codegen disabled, fall through to today's
    # generic-chain path.
    #
    # The type annotation is left as `Any` to avoid a circular import
    # (codegen.py imports from ir.py).  In practice this is a
    # `synth.lean_backend.codegen.HelperRegistry` instance.
    helper_registry: object | None = None
    # COST_INVS §1 — resource-bound invariants.  When `cost_target` is
    # set to an expression string over the input variables, the
    # synthesizer additionally emits cost-bound proof obligations:
    #   (A) cost-lb     : τ ⇒ cost@L ≥ 0
    #   (B) cost-decrement: τ ∧ g ∧ trans ⇒ cost@L(pre) ≥ body_cost +
    #                        cost@L(post)
    #   (C) cost-budget : Pre(input) ⇒ cost@L(initial state) ≤ cost_target
    # Candidates for cost@L holes come from `atoms["cost@<lid>"]`
    # (same shape as `phi@<lid>` candidates).  When `cost_target` is
    # None (default), no cost-bound obligations are emitted — preserves
    # backward compatibility for all existing benchmarks.
    cost_target: str | None = None
    # Per-constraint wedge detection.  When a single safety
    # constraint accumulates this many Lean dispatches WITHOUT
    # finding a validating subset, the solver prints a one-time
    # `[WEDGE]` warning naming the constraint and a sample
    # failure-dump path — signal that the user should likely
    # author a Tier-3 helper.  At 2× this threshold, the solver
    # ABANDONS enumeration on that constraint, marks it
    # `needs-helper`, finishes the other constraints, and
    # returns NoSolution(reason="needs-helpers") with a clear
    # hint listing the wedged constraints.  Set to `None` to
    # disable.
    #
    # Default bumped 30 → 200 (community-validation finding F7,
    # 2026-06-08).  Rationale: with `.solved.lean` cache as the
    # primary authoring path, partial-subset enumeration can
    # need ~hundreds of dispatches per constraint before
    # reaching the full-τ cube that matches the cache.  At 30
    # dispatches, the wedge detector ABANDONED constraints
    # before the cache hit could land — agents saw
    # `needs-helpers` despite having correct cached proofs.
    # 200 is well above fib's per-constraint dispatch count
    # (~tens per) but well below the wedge-loop's natural
    # divergence point for genuinely-needs-helpers cases.
    # Bench authors who need a tighter wedge can set this
    # explicitly per-problem.
    wedge_threshold: int | None = 200

    def __post_init__(self) -> None:
        # F12 — community-validation finding (2026-06-08): UF names
        # that collide with Lean 4 reserved words produce a parse
        # error in the dispatched theorem, surfacing as a wedge
        # rather than a helpful early message.  The v3 Q3 agent hit
        # this with `matches`; renaming to `hits` resolved it.  Fail
        # fast at Problem-construction time so authors find the bug
        # before the first synth run.
        _LEAN_RESERVED = frozenset({
            "match", "matches", "with", "where", "do",
            "if", "then", "else", "let", "in", "fun", "have",
            "by", "as", "at", "from", "show", "suffices",
            "def", "theorem", "axiom", "lemma", "example",
            "inductive", "structure", "class", "instance",
            "namespace", "section", "open", "import", "prelude",
            "end", "mutual", "partial", "unsafe", "private",
            "protected", "noncomputable", "variable", "variables",
            "universe", "Type", "Sort", "Prop", "Pi",
            "forall", "exists", "term", "tactic", "command",
            "set_option", "attribute", "deriving", "extends",
            "abbrev", "constant", "syntax", "macro", "elab",
            "false", "true",
        })
        for uf_decl in self.uninterpreted:
            uf_name = uf_decl[0]
            if uf_name in _LEAN_RESERVED:
                raise ValueError(
                    f"Uninterpreted-function name {uf_name!r} collides "
                    f"with a Lean 4 reserved word.  The Lean backend "
                    f"emits `axiom {uf_name} : ...` and `lake env lean` "
                    f"will fail to parse the theorem.  Rename the UF; "
                    f"common safe alternatives: `_{uf_name}`, "
                    f"`{uf_name}_uf`, or a domain synonym (e.g. "
                    f"`matches` → `hits`, `class` → `cls`).  "
                    f"Community-validation finding F12 (2026-06-08)."
                )

        # F19 — community-validation finding (2026-06-08):
        # `dump_lean_failures_dir` is resolved as CWD-relative
        # at Problem construction.  Running benchmarks from a
        # subdir silently misplaces dumps + cache hits.
        # Normalize to abspath here so the resolved location is
        # stable regardless of any subsequent CWD changes, and
        # print it once to stderr so the author can verify.
        if (self.dump_lean_failures_dir is not None
                and not _is_absolute_path(self.dump_lean_failures_dir)):
            import os
            import sys
            resolved = os.path.abspath(self.dump_lean_failures_dir)
            print(
                f"[INFO] dump_lean_failures_dir resolved to "
                f"{resolved} (was relative: "
                f"{self.dump_lean_failures_dir!r}).  Run from "
                f"the repo/worktree root if this looks wrong.",
                file=sys.stderr,
            )
            # `frozen=False` dataclass: direct attribute write
            # is supported.  Use object.__setattr__ to avoid
            # custom-setattr surprises if Problem ever becomes
            # frozen.
            object.__setattr__(self, "dump_lean_failures_dir", resolved)

        # F3 — community-validation finding (2026-06-08): if
        # `dump_lean_failures_dir` points at an EXISTING corpus
        # benchmark's dump dir, the new benchmark's failed.lean
        # dumps pollute the other benchmark's artifacts and the
        # author's helpers may collide.  Warn early.  Example
        # failure mode: a `gcd_lcm` benchmark mistakenly sets
        # `dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/gcd"`
        # — the existing `gcd` benchmark's dump dir gets
        # repurposed.
        #
        # Heuristic: warn ONLY when the dump dir contains a
        # Helpers.lean whose `namespace` declaration names a
        # DIFFERENT benchmark from the dir.  Helpers files
        # without an explicit namespace are ambiguous and not
        # flagged (would false-positive on existing benchmarks
        # like gale_shapley/Helpers.lean which uses module-
        # qualified names instead of an open namespace).
        if self.dump_lean_failures_dir is not None:
            import os
            import re
            d = self.dump_lean_failures_dir
            helpers_path = os.path.join(d, "Helpers.lean")
            if os.path.isfile(helpers_path):
                dir_name = os.path.basename(os.path.normpath(d))
                try:
                    with open(helpers_path) as f:
                        contents = f.read()
                    m = re.search(
                        r"^namespace\s+SynthLean\.Y2Corpus\.(\w+)",
                        contents, flags=re.MULTILINE,
                    )
                    # Normalize before comparing: snake_case dir vs
                    # CamelCase namespace is a common project convention
                    # (e.g., dir `gale_shapley` ↔ namespace `GaleShapley`).
                    # Strip underscores and lowercase both sides.
                    def _norm(s: str) -> str:
                        return s.replace("_", "").lower()
                    if m and _norm(m.group(1)) != _norm(dir_name):
                        import sys
                        print(
                            f"[WARNING] dump_lean_failures_dir='{d}' "
                            f"contains a Helpers.lean whose namespace "
                            f"is SynthLean.Y2Corpus.{m.group(1)}, not "
                            f"`{dir_name}`.  This is the naming-collision "
                            f"footgun (community-validation finding F3).  "
                            f"Verify the dir name matches your benchmark; "
                            f"running synth will pollute the other "
                            f"benchmark's dumps.  See `problem.skill` "
                            f"~'naming-collision' for the failure mode.",
                            file=sys.stderr,
                        )
                except OSError:
                    pass

    @property
    def all_vars(self) -> list[Var]:
        return list(self.inputs) + list(self.outputs) + list(self.locals)

    @property
    def var_by_name(self) -> dict[str, Var]:
        return {v.name: v for v in self.all_vars}
