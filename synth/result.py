"""Three-outcome result types for the synthesizer.

Defined per DESIGN.md §6:

  SolveResult  →  one or more concrete solutions (sorted by score).
  NoSolution   →  Z3 returned unsat — predicate space too strict;
                  carries channels for the LLM outer loop to refine.
  Timeout      →  Z3 timed out — predicate space too loose / too big;
                  carries hole sizes and partial solutions.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Any, Union


# ─────────────────────────────────────────────────────────────────────
# Lean-dispatch telemetry (Ring 2 / Phase X).
# ─────────────────────────────────────────────────────────────────────
@dataclass
class LeanDispatchStats:
    """Counts of Lean-fallthrough verification outcomes during a
    single `solve()` call.  Reported on every Result type
    (SolveResult / NoSolution / Timeout) so regression tests can
    track whether the Lean path is actually doing work.

    - `valid`: Lean proved a Z3-UNKNOWN class.  This is the
      headline number — every increment is a class that's
      genuinely verified (not lenient-accepted).
    - `unknown`: Lean tried but couldn't close the proof.
    - `errors`: Lean failed for a reason other than tactic
      failure (translation bug, build infrastructure issue).
    """
    valid:   int = 0
    unknown: int = 0
    errors:  int = 0

    @property
    def total(self) -> int:
        return self.valid + self.unknown + self.errors

    def to_dict(self) -> dict:
        return {"valid": self.valid, "unknown": self.unknown,
                "errors": self.errors}


# ─────────────────────────────────────────────────────────────────────
# A single synthesized candidate.
# ─────────────────────────────────────────────────────────────────────
@dataclass
class Solution:
    """One concrete instantiation of every hole.

    `choices` maps hole_id → atom index (into the original atom list
    in `Problem.atoms`).  `atoms` maps hole_id → the chosen atom
    (string for predicates / numeric expressions, dict for transitions).
    `code` is the pretty-printed program for inspection.
    `score` is the heuristic ranking metric (lower is better);
    `score_components` exposes the breakdown for transparency.
    """
    choices: dict[str, int]
    atoms: dict[str, Any]
    code: str = ""
    score: float = 0.0
    score_components: dict[str, float] = field(default_factory=dict)


# ─────────────────────────────────────────────────────────────────────
# Successful outcome.
# ─────────────────────────────────────────────────────────────────────
@dataclass
class SolveResult:
    """One or more solutions, sorted ascending by `score`."""
    solutions: list[Solution]
    # Ring 2: Lean-fallthrough telemetry.  `hints` is human-readable
    # lines; `lean_dispatch` is the structured form for regression
    # tests.  Both empty / zero when no dispatch fired (default
    # `accept`-mode benchmarks, or potentially_unsound=False
    # benchmarks where Z3 alone decided everything).
    hints: list[str] = field(default_factory=list)
    lean_dispatch: LeanDispatchStats = field(default_factory=LeanDispatchStats)

    def __bool__(self) -> bool:
        return bool(self.solutions)

    @property
    def best(self) -> Solution:
        return self.solutions[0]


# ─────────────────────────────────────────────────────────────────────
# Failure outcomes — first-class, with structured telemetry for the
# LLM refinement loop (plan §6.2, §6.3).
# ─────────────────────────────────────────────────────────────────────
@dataclass
class NoSolution:
    """Z3 returned unsat.  Likely cause: predicate space too strict.

    `unsat_core`        — names of assertions Z3 identified as the core.
    `pinned_unknowns`   — per hole, the atoms that were viable in any
                          partial relaxation we tried (empty in Phase 1.A;
                          populated in later phases once we add CEGAR-like
                          refinement of the atom space).
    `witness_paths`     — paths that failed (populated in PINS / Phase 4).
    `hints`             — heuristic suggestions for the LLM.
    """
    reason: str = "unsat"
    unsat_core:        list[str]            = field(default_factory=list)
    pinned_unknowns:   dict[str, list[int]] = field(default_factory=dict)
    witness_paths:     list[str]            = field(default_factory=list)
    hints:             list[str]            = field(default_factory=list)
    lean_dispatch:     LeanDispatchStats    = field(default_factory=LeanDispatchStats)

    def __bool__(self) -> bool:
        return False


@dataclass
class Timeout:
    """Z3 timed out.  Likely cause: predicate space too loose / too large.

    `hole_sizes`        — atom-list length per hole (signals where to prune).
    `expensive_queries` — (assertion id, seconds) tuples that stalled Z3
                          (populated when per-query profiling is wired up).
    `partial_solutions` — any solutions we found before timing out.
    `hints`             — heuristic suggestions for the LLM.
    """
    reason: str = "timeout"
    budget_seconds:    float                       = 0.0
    hole_sizes:        dict[str, int]              = field(default_factory=dict)
    expensive_queries: list[tuple[str, float]]     = field(default_factory=list)
    partial_solutions: list[Solution]              = field(default_factory=list)
    hints:             list[str]                   = field(default_factory=list)
    lean_dispatch:     LeanDispatchStats           = field(default_factory=LeanDispatchStats)

    def __bool__(self) -> bool:
        return False


Result = Union[SolveResult, NoSolution, Timeout]
