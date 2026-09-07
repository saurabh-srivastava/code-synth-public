"""Solver — PLDI'09 attribute-class reduction (Phase 3.X.2).

The previous CEGIS approach searches indicator assignments and verifies
each candidate, blocking bad ones one at a time.  That is O(search-space)
in the worst case and wedged for any non-trivial predicate space (see
CLAUDE.md lessons #8, #9).

PLDI'09's reduction sidesteps the ∃b. ∀V. sc(b,V) shape by precomputing,
for each safety constraint, which indicator assignments make it valid.
Each check is a *single* Z3 unsat-of-negation query — Z3's strong side.

Pipeline:

  1. For each `SafetyConstraint sc`:
        a. Collect the indicator booleans that occur in `sc.body`.
        b. Group them by hole.  τ holes enumerate every subset;
           non-τ holes are single-hot (one True at a time).
        c. For each assignment in the Cartesian product, substitute the
           Boolean values into `sc.body`, conjoin with the axioms,
           negate, and ask Z3 for SAT.  `unsat` ⇒ this attribute class
           is *valid* for this constraint.
  2. Encode valid attribute classes as Boolean clauses:
        for each c, add `⋁_{valid assignment A_c}  ⋀_{b ∈ A_c.dom} b == A_c[b]`.
  3. Add the well-formedness constraints (PbEq single-hot on non-τ holes).
  4. Z3 SAT-solves the result.  Each model is a valid synthesis
     solution by construction — no per-candidate verification needed.
  5. Enumerate top-K by adding standard differ-by-one blockers between
     solves.
"""
from __future__ import annotations
import time
import itertools
from itertools import product
from typing import Any

import os
from concurrent.futures import ThreadPoolExecutor, as_completed

import z3

from .ir import Problem
from .expand import expand
from .constraints import generate, SafetyConstraint, AtomRef
from .decode import decode
from .result import (
    SolveResult, NoSolution, Timeout, Solution, Result, LeanDispatchStats
)

# Cap parallelism at half the CPU count (be nice to the machine).
# Lean dispatch is subprocess-bound, so threads (which release the
# GIL during subprocess.run) suffice — no need for a process pool.
_LEAN_PARALLEL_WORKERS = max(1, (os.cpu_count() or 4) // 2)
# Halved from cpu_count to cpu_count//2 (2026-05-19) for CI
# stability: ubuntu-latest runners had a SIGSEGV on
# bresenham_full's subprocess under workers=cpu_count, likely
# from Z3 memory pressure when N Lean processes load mathlib
# olean each.  Marginal local slowdown (kadane 37s → ~50s) is
# worth the stable CI signal.

# Ring 2 — Lean as UNKNOWN-fallthrough verifier.  Imported at module
# level; the lake-env-lean call only happens on Z3 UNKNOWN, AND only
# when `lean_available()` (cheap check for toolchain reachability).
# Lean fallthrough is always-on when available — see SOUNDNESS.md.
try:
    from .lean_backend import verify_class_via_lean, lean_available
    _LEAN_AVAILABLE_AT_IMPORT = True
except ImportError:
    _LEAN_AVAILABLE_AT_IMPORT = False


# Per attribute-class check budget.  Each call is quantifier-free in V
# (modulo axiom quantifiers); typical checks are milliseconds.
_PER_CHECK_TIMEOUT_MS = 10_000


# Constraint kinds whose validity check, if it returns Z3 UNKNOWN,
# we conservatively REJECT (the attribute class is treated as invalid).
#
# **Historical context (CLAUDE.md lesson #10)**: the original policy
# was conservative-ACCEPT for ALL UNKNOWN responses.  Rationale:
# axiom-heavy benchmarks like `fib` rely on Z3 not always being able
# to prove validity in budget, and rejecting those UNKNOWNs would
# spuriously fail synthesis.
#
# **P2 refinement (RESEARCH.md §O)**: ranking + safety +
# coverage all carry soundness obligations.  A false-positive
# (accept an UNKNOWN that's actually invalid) gives a synthesized
# program that fails at runtime — the Python emitter's runtime
# checks expose this immediately (Lesson #32).  A false-negative
# just means a benchmark might fail to synthesize and the user
# supplies a different atom set.  For all the kinds we currently
# emit, the asymmetry favors REJECT.
#
# To keep axiom-heavy benchmarks (fib) working when Z3 never
# returns unsat on its validity checks, the policy is *two-pass*:
# strict-REJECT first, lenient-ACCEPT fallback if the strict pass
# leaves a constraint with zero valid classes.  Implementation in
# the per-constraint enumeration block below.
_REJECT_UNKNOWN_KINDS = {
    "safety",
    "safety-bundle-entry",
    "safety-bundle-post",
    "coverage",
    "ranking-decrease",
    "ranking-lb",
    "ranking-proc-decrease",
    "ranking-proc-lb",
    # COST_INVS §1 — cost-bound obligations are soundness-critical:
    # an UNKNOWN here cannot be promoted to "valid" without violating
    # the cost-budget claim.
    "cost-lb",
    "cost-decrement",
    "cost-budget",
}

# Kinds the Lean translator currently handles.  Chain-bundle
# constraints come in two shapes — entry (Fpre ∧ chain ⇒ τ_loop)
# and post (Fpre ∧ chain ⇒ Fpost) — handled by different
# translators in `synth.lean_backend.translate`.  See `verify.py`
# for the dispatch.
_LEAN_TRANSLATABLE_KINDS = {
    "safety",
    "safety-bundle-entry",
    "safety-bundle-post",
    "ranking-decrease",
    "ranking-lb",
    "coverage",
    # COST_INVS §2 wiring: cost-* obligations route through Lean
    # when Z3 returns UNKNOWN.  CostLemmas.lean's named identities
    # close polynomial cost-decrement obligations that Z3-NIA wedges
    # on.  cost-budget remains on Z3 (translator deferred).
    "cost-lb",
    "cost-decrement",
}

# Subset of _LEAN_TRANSLATABLE_KINDS that go through the axiom-heavy
# "skip Z3, dispatch ALL classes to Lean" path.  These are the kinds
# where Z3's quantifier-instantiation heuristic produces unreliable
# verdicts on axiom-heavy obligations (per `_axiom_heavy_lean_path`
# rationale below).
#
# Ranking obligations (`ranking-lb`, `ranking-decrease`) ARE
# included even though they're structurally linear — when the
# benchmark has UF axioms in scope, Z3's verifier carries those
# axioms and quantifier instantiation can produce spurious UNKNOWNs
# on otherwise-trivial linear checks (observed on majority_element
# ranking-lb: Z3 UNKNOWN on multiple τ subsets due to count_eq
# axiom interference, breaking the per-constraint cube list).
# Lean's `omega` tactic dispatches linear rankings reliably
# regardless of axioms in scope — slower per call but consistent.
_AXIOM_HEAVY_DISPATCH_KINDS = {
    "safety",
    "safety-bundle-entry",
    "safety-bundle-post",
    "coverage",
}


def solve(problem: Problem) -> Result:
    # Validate that helper_registry (if set) is wired correctly.
    # Without the corresponding SynthLean.lean import line, every
    # Lean dispatch fails with `unknown identifier <helper>` and
    # synth wedges with needs-helpers.  Catching this BEFORE any
    # dispatch saves the user 10+ minutes of debugging timeouts.
    # See codegen.py:HelperRegistry.validate_synthlean_import +
    # problem.skill "Importing into the lake build".
    if problem.helper_registry is not None:
        try:
            from .lean_backend.codegen import HelperRegistry as _HR_validate
            if isinstance(problem.helper_registry, _HR_validate):
                warning = problem.helper_registry.validate_synthlean_import()
                if warning:
                    import sys
                    print(f"[WARNING] {warning}", file=sys.stderr)
        except Exception:
            # Best-effort — don't block the synth on a bad validator.
            pass

    scaffold = expand(problem)
    system = generate(problem, scaffold)

    all_indicators = [b for bs in system.indicators.values() for b in bs]
    all_indicators_set = {b.get_id() for b in all_indicators}
    indicator_to_hole: dict[int, str] = {
        b.get_id(): hid
        for hid, bs in system.indicators.items()
        for b in bs
    }

    # ── Step 1+2: enumerate valid attribute classes per constraint. ──
    start = time.monotonic()
    total_checks = 0
    unknown_checks = 0
    # F18 (community-validation 2026-06-08): per-sc UNKNOWN
    # tracking so the final hint can name the bottleneck
    # constraint(s) instead of just "1 attribute-class
    # returned 'unknown'".  Maps sc_idx → {kind, loop_id,
    # branch_idx, count}.
    unknown_details: dict[int, dict] = {}
    # F14 (community-validation 2026-06-08): one-time sc0 UF
    # cliff warning latch — fires on the FIRST unknown for
    # sc0 with an entry-bundle kind if the benchmark has a UF.
    _sc0_uf_cliff_warned = False
    # F16 (community-validation 2026-06-08): per-sc consecutive
    # UNKNOWN counter for the adaptive timeout.  Reset to 0 on
    # any VALID dispatch for that sc.  When ≥ 3 consecutive
    # UNKNOWNs, subsequent dispatches use a 5s budget instead of
    # 15s — the cold-cache window has passed and these are the
    # enumeration treadmill (genuinely unprovable partial-τ
    # subsets).
    consecutive_unknowns_per_sc: dict[int, int] = {}

    def _record_unknown(sc_idx: int, sc) -> None:
        """Bump per-sc + global UNKNOWN counters, emit F14 sc0
        UF cliff warning on first sc0 entry-bundle UNKNOWN if
        the benchmark has a UF."""
        nonlocal unknown_checks, _sc0_uf_cliff_warned
        unknown_checks += 1
        info = unknown_details.get(sc_idx)
        if info is None:
            unknown_details[sc_idx] = {
                "kind": sc.kind,
                "loop_id": getattr(sc, "loop_id", None),
                "branch_idx": getattr(sc, "branch_idx", None),
                "count": 1,
            }
        else:
            info["count"] += 1
        consecutive_unknowns_per_sc[sc_idx] = (
            consecutive_unknowns_per_sc.get(sc_idx, 0) + 1
        )
        # F14 — sc0 UF cliff: an entry-bundle obligation with a
        # UF application equation in τ frequently times out on
        # the FIRST dispatch (cold mathlib + omega/nlinarith
        # can't rewrite UF axioms; simp_all is slow and may not
        # converge in budget).  If sc0 is entry-bundle AND
        # problem has a UF declared, surface the actionable
        # advice once.
        if (not _sc0_uf_cliff_warned
                and sc_idx == 0
                and sc.kind == "safety-bundle-entry"
                and problem.uninterpreted):
            _sc0_uf_cliff_warned = True
            _uf_names = ", ".join(uf[0] for uf in problem.uninterpreted)
            print(
                f"[F14] sc0 entry-bundle UNKNOWN with UF in "
                f"scope (UFs: {_uf_names}).  The generic tactic "
                f"chain often can't rewrite UF axioms within "
                f"budget on a cold mathlib.  Consider authoring "
                f"`sc0_fallthrough_<hash>.solved.lean` upfront "
                f"with a one-line proof "
                f"(e.g. `exact (user_axiom_0 args).symm`).  See "
                f"problem.skill REC 11.7.A.",
                flush=True,
            )

    def _adaptive_timeout_s(sc_idx: int) -> float:
        """F16 adaptive timeout: drop per-class Lean budget to
        5s after 3 consecutive Z3-UNKNOWNs on this sc.  Reset
        to 15s on first VALID dispatch.  Rationale: after 3
        unknowns we're past the cold-cache window (mathlib is
        loaded) and on the enumeration treadmill — these
        partial-τ subsets are genuinely unprovable and burning
        15s × hundreds is wasted wall-clock.
        """
        return 5.0 if consecutive_unknowns_per_sc.get(sc_idx, 0) >= 3 else 15.0

    clauses: list[z3.ExprRef] = []

    # One reusable verifier solver with axioms pre-asserted.  Each
    # attribute-class check uses push/pop around the negated body —
    # saves re-asserting the (often expensive) axioms hundreds of
    # times per benchmark.  Phase 3.X.3.
    verifier = z3.Solver()
    verifier.set("timeout", _PER_CHECK_TIMEOUT_MS)
    for ax in system.axioms:
        verifier.add(ax)

    # Periodic progress printing for long-running synths.  Every
    # `progress_every_n_dispatches` Lean dispatches OR
    # `progress_every_n_seconds`, whichever fires first, print a
    # one-line `[PROGRESS]` summary so the user can see what
    # the synth is doing during multi-minute or multi-hour runs.
    progress_every_n_dispatches = 50
    progress_every_n_seconds = 30.0
    last_progress_at_dispatch = 0
    last_progress_at_time = time.monotonic()

    def _maybe_print_progress(sc_idx: int, sc, force: bool = False) -> None:
        """Print a `[PROGRESS]` line if enough time / dispatches
        elapsed since the last one.  Called from the dispatch
        callbacks; throttles so we get ~one line per 30s or per
        50 Lean calls, whichever is sooner.
        """
        nonlocal last_progress_at_dispatch, last_progress_at_time
        total_dispatches = (lean_dispatch_hits + lean_dispatch_misses
                            + lean_dispatch_errors)
        elapsed = time.monotonic() - last_progress_at_time
        delta_n = total_dispatches - last_progress_at_dispatch
        if not force and delta_n < progress_every_n_dispatches \
                and elapsed < progress_every_n_seconds:
            return
        print(
            f"[PROGRESS] {time.monotonic() - start:6.0f}s | "
            f"sc{sc_idx}/{len(system.safety)-1} "
            f"({sc.kind}, "
            f"loop_id={getattr(sc, 'loop_id', None)}, "
            f"branch_idx={getattr(sc, 'branch_idx', None)}) | "
            f"dispatches: {lean_dispatch_hits}V / "
            f"{lean_dispatch_misses}U / "
            f"{lean_dispatch_errors}E / "
            f"{total_dispatches} total | "
            f"helper: {helper_dispatch_hits} | "
            f"wedges: {len(wedge_abandoned)} abandoned",
            flush=True,
        )
        last_progress_at_dispatch = total_dispatches
        last_progress_at_time = time.monotonic()

    # Per-constraint stats for the monotonicity-aware fast path.
    free_tau_hits = 0
    free_tau_misses = 0
    # Per-constraint wedge detection.  When a single constraint
    # accumulates `wedge_threshold` Lean dispatches WITHOUT a
    # validating subset, print a one-time `[WEDGE]` warning naming
    # the constraint + a sample dump path.  At `2 × threshold` we
    # ABANDON further Lean dispatches on that constraint (subsequent
    # calls defer immediately), so other constraints can finish and
    # the run terminates with a `needs-helpers` NoSolution naming
    # the wedged constraints.  Threshold counts only non-VALID
    # outcomes — a class that validates resolves enumeration and
    # doesn't indicate a wedge.
    wedge_dispatch_counts: dict[int, int] = {}
    wedge_warned: set[int] = set()
    wedge_abandoned: set[int] = set()
    wedge_details: dict[int, dict] = {}
    # Per-constraint: count of dispatches that found a VALID
    # class.  Used to suppress ABANDONMENT — if a constraint
    # has discovered ANY valid class, we keep enumerating;
    # the framework will use what we've found even if many
    # subsets fail.  Only abandon when no valid has surfaced
    # at all (the truly-wedged case).
    wedge_valid_counts: dict[int, int] = {}

    def _wedge_track(sc_idx: int, sc, status: str, dump_dir) -> bool:
        """Tally a Lean dispatch outcome for wedge detection.
        Returns True iff this constraint has been ABANDONED — the
        caller should skip further Lean work on it.

        Abandonment policy (2026-05-25 fix after array_product
        regression): only abandon if `2 × threshold` non-valid
        dispatches AND zero valid dispatches.  A constraint that
        eventually validates some subset is NOT wedged — the
        framework will assemble cubes from what it found.  This
        avoids false-flagging axiom-heavy benchmarks where the
        per-class enumeration tries many failing subsets before
        reaching a validating one.
        """
        if problem.wedge_threshold is None:
            return sc_idx in wedge_abandoned
        if sc_idx in wedge_abandoned:
            return True
        if status == "valid":
            wedge_valid_counts[sc_idx] = (
                wedge_valid_counts.get(sc_idx, 0) + 1
            )
            # F16: any VALID dispatch resets the consecutive-
            # UNKNOWN counter — we're not on the enumeration
            # treadmill for this sc.  Subsequent dispatches go
            # back to the 15s budget.
            consecutive_unknowns_per_sc[sc_idx] = 0
            return False
        wedge_dispatch_counts[sc_idx] = (
            wedge_dispatch_counts.get(sc_idx, 0) + 1
        )
        n = wedge_dispatch_counts[sc_idx]
        if n == problem.wedge_threshold and sc_idx not in wedge_warned:
            wedge_warned.add(sc_idx)
            _sample = ""
            if dump_dir is not None:
                _sample = (f" ; inspect `ls {dump_dir}/"
                           f"sc{sc_idx}_fallthrough_*.failed.lean | head`")
            print(
                f"[WEDGE] sc{sc_idx} (kind={sc.kind}, "
                f"loop_id={getattr(sc, 'loop_id', None)}, "
                f"branch_idx={getattr(sc, 'branch_idx', None)}): "
                f"{n} non-valid Lean dispatches; consider authoring a "
                f"Tier-3 helper{_sample}.",
                flush=True,
            )
        # ABANDON only when 2× threshold non-valid AND zero valid
        # — otherwise this constraint IS making progress; let it
        # keep enumerating.
        if (n >= 2 * problem.wedge_threshold
                and wedge_valid_counts.get(sc_idx, 0) == 0
                and sc_idx not in wedge_abandoned):
            wedge_abandoned.add(sc_idx)
            wedge_details[sc_idx] = {
                "kind": sc.kind,
                "loop_id": getattr(sc, "loop_id", None),
                "branch_idx": getattr(sc, "branch_idx", None),
                "dispatches": n,
                "dump_dir": str(dump_dir) if dump_dir else None,
            }
            print(
                f"[WEDGE] sc{sc_idx}: ABANDONING after {n} dispatches "
                f"(0 valid found).  Run will return needs-helpers.",
                flush=True,
            )
            return True
        return False

    # Per-constraint deferred classes.  Constraints whose validity
    # check returned Z3 UNKNOWN go here (when sc.kind is in
    # _REJECT_UNKNOWN_KINDS).  Two-level fallback:
    #   (a) Per-constraint: if strict-REJECT leaves a constraint with
    #       zero confirmed-valid classes, promote its deferred classes
    #       in-place.  This handles the case where ONLY UNKNOWNs ever
    #       come back (rare).
    #   (b) Global: if the strict-pass main-SAT returns UNSAT, retry
    #       with ALL deferred classes promoted.  This handles the
    #       axiom-heavy case (fib) where some constraints confirm a
    #       few valid classes but the right answer is among the
    #       UNKNOWN-deferred ones.
    # `unknown_fallback_constraints` was tracked by the excised
    # lenient promotion paths; with sound-mode-only semantics it
    # would always be empty, so it's removed entirely.

    # Ring 2: Lean fallthrough telemetry.
    lean_dispatch_hits = 0
    lean_dispatch_misses = 0
    lean_dispatch_errors = 0
    # §H.2 codegen helper-citation telemetry.  `helper_hits` counts
    # dispatches that closed via a Tier-3 helper citation (~2s
    # fast path); `helper_misses` counts dispatches that ran the
    # generic tactic chain (no matching helper, or helper didn't
    # apply to this τ subset).  Ratio is the "coverage" — how much
    # of the enumeration the codegen path absorbed.
    helper_dispatch_hits = 0
    helper_dispatch_misses = 0
    # Per-constraint: (strict cubes, extra cubes if lenient).  The
    # strict variant uses only confirmed-valid; the lenient variant
    # additionally allows UNKNOWN-deferred classes.
    per_constraint_cubes: list[tuple[list[z3.ExprRef], list[z3.ExprRef]]] = []

    for sc_idx, sc in enumerate(system.safety):
        relevant = _collect_relevant(sc.body, all_indicators_set, all_indicators)

        if not relevant:
            # Constraint depends on no indicators.  Either always-valid
            # or always-invalid (an UNSAT regardless of indicators).
            n_checks, vr = _check_validity(sc.body, verifier)
            total_checks += n_checks
            if vr == z3.unknown:
                _record_unknown(sc_idx, sc)
                continue  # treat unknown as "potentially valid"
            if vr == z3.sat:
                # ¬body satisfiable → constraint invalid regardless.
                return NoSolution(
                    reason="unsat",
                    unsat_core=[],
                    hints=[
                        f"Safety constraint #{sc_idx} ({sc.kind}) is invalid "
                        "for every indicator assignment — predicate space "
                        "lacks the atoms needed to prove this obligation."
                    ],
                )
            # unsat → constraint trivially valid; no clause needed.
            continue

        # Group relevant indicators by hole.
        rel_by_hole: dict[str, list[z3.BoolRef]] = {}
        for b in relevant:
            rel_by_hole.setdefault(indicator_to_hole[b.get_id()], []).append(b)

        # Phase 3.L: per-constraint monotonicity classification.
        # For each τ hole, if ALL of its in-body atoms appear in a single
        # position (only antecedent OR only consequent), the hole's
        # validity is monotone in that direction:
        #   * CONS-only: validity is monotone-downward in the τ subset
        #     (more conjuncts in the consequent ⇒ harder to prove).
        #     Hardest case = all atoms True.
        #   * ANT-only: validity is monotone-upward (more conjuncts in
        #     the antecedent ⇒ easier to prove).  Hardest case = all
        #     atoms False (no τ contribution to the premise).
        # If the hardest case passes for a given assignment to the OTHER
        # holes, ALL 2^|atoms| subsets of the free τ pass too — saving
        # the per-subset enumeration.  The cube emitted in that case
        # excludes the free-τ indicators, leaving them unconstrained in
        # the main SAT (which the well-formedness layer still
        # constrains: τ holes have no PbEq, so all-True or all-False
        # subsets are globally feasible).
        classification = _classify_atoms(sc)

        free_taus: list[tuple[str, list[z3.BoolRef], bool]] = []
        other_holes: list[tuple[str, list[z3.BoolRef]]] = []
        for hid, bs in rel_by_hole.items():
            pos = _free_tau_position(hid, bs, classification)
            if pos is not None:
                free_taus.append((hid, bs, pos))
            else:
                other_holes.append((hid, bs))

        # Build per-OTHER-hole assignment lists (the holes we still
        # enumerate fully).
        per_hole_assignments: list[list[dict[z3.BoolRef, bool]]] = []
        # Track which τ holes are BOTH-position (vs single-hot).
        #
        # ⚠️  INFRASTRUCTURE FOR THE DISABLED §H.2 FAST PATH ⚠️
        # `both_tau_hole_indices`, `sh_hole_indices`, and
        # `all_true_both_tau` below were added for the unsat-core-
        # inspired fast path in RESEARCH.md §H.2.  That prototype is
        # HARD-DISABLED below (`_fast_path_enabled = False`) because
        # it is UNSOUND for benchmarks with BOTH-position distractor
        # atoms — see RESEARCH.md §H.2.PROTOTYPE for the detailed
        # caveats.  DO NOT just flip the flag.  Read the prototype
        # findings first.  The infrastructure is preserved as a
        # starting point for a future iteration (bottom-up
        # enumeration / Z3 ALL-SAT / core minimization).
        both_tau_hole_indices: list[int] = []
        sh_hole_indices: list[int] = []
        for i, (hid, bs) in enumerate(other_holes):
            if hid.startswith("tau@"):
                hole_options = []
                for mask in range(1 << len(bs)):
                    assign = {b: bool((mask >> i_) & 1) for i_, b in enumerate(bs)}
                    hole_options.append(assign)
                both_tau_hole_indices.append(i)
            else:
                # Single-hot.  Each in-body indicator True OR all-False
                # (out-of-body indicator True under global PbEq).
                hole_options = []
                for j in range(len(bs)):
                    assign = {b: (i_ == j) for i_, b in enumerate(bs)}
                    hole_options.append(assign)
                hole_options.append({b: False for b in bs})
                sh_hole_indices.append(i)
            per_hole_assignments.append(hole_options)

        # All-True assignment for BOTH-position τ atoms.  Used by the
        # DISABLED §H.2 prototype below.  See the comment block above
        # `both_tau_hole_indices` and RESEARCH.md §H.2.PROTOTYPE for
        # why it's disabled.
        all_true_both_tau: dict[z3.BoolRef, bool] = {}
        for i_ in both_tau_hole_indices:
            _, bs = other_holes[i_]
            for b in bs:
                all_true_both_tau[b] = True

        # Pre-compute the "hardest" assignment for the free τ holes and
        # the per-hole subset options used as a fallback when the
        # hardest case fails.
        hardest_free_assign: dict[z3.BoolRef, bool] = {}
        free_tau_subset_options: list[list[dict[z3.BoolRef, bool]]] = []
        for hid, bs, pos in free_taus:
            for b in bs:
                hardest_free_assign[b] = pos
            subset_opts = []
            for mask in range(1 << len(bs)):
                subset_opts.append(
                    {b: bool((mask >> i) & 1) for i, b in enumerate(bs)}
                )
            free_tau_subset_options.append(subset_opts)

        # Enumerate Cartesian product over OTHER holes, with the
        # monotonicity fast path on free τ holes.
        #
        # Each attribute class either CONFIRMS valid (Z3 unsat on the
        # negation), DEFERS as unknown (Z3 unknown — might be valid
        # or invalid), or fails (Z3 sat → constraint refuted).
        #
        # For kinds in _REJECT_UNKNOWN_KINDS, UNKNOWN is treated as
        # "deferred" — we hold those classes back from
        # `valid_assignments` and only promote them if NO confirmed
        # classes remain (the two-pass fallback below).  This gives
        # us the strongest soundness signal we can without breaking
        # axiom-heavy benchmarks (fib) where every check returns
        # UNKNOWN.
        valid_assignments: list[dict[z3.BoolRef, bool]] = []
        unknown_deferred: list[dict[z3.BoolRef, bool]] = []

        # ─── General helper short-circuit (RESEARCH.md §H.2.CODEGEN) ──
        # Before any enumeration, check if a Tier-3 helper covers the
        # FULL τ subset.  If yes, dispatch ONCE; on VALID, emit only
        # the full-τ cube and SKIP enumeration entirely.
        #
        # This mirrors the short-circuit inside `_axiom_heavy_lean_path`
        # below but ALSO fires for non-axiom-heavy benchmarks (e.g.,
        # insertion_sort) where the chain-aware translator generates
        # obligations that the generic tactic chain can't close —
        # without a helper, the synth would dispatch Lean per Z3-
        # UNKNOWN subset.
        _general_short_circuit = False
        if (problem.helper_registry is not None
                and sc.kind in _LEAN_TRANSLATABLE_KINDS
                and _LEAN_AVAILABLE_AT_IMPORT
                and lean_available()
                # coverage at procedure-level has loop_id=None by design
                and (sc.kind == "coverage"
                     or _extract_loop_id(sc) is not None)):
            _loop_id_sc = _extract_loop_id(sc)
            _full_assign: dict[z3.BoolRef, bool] = {}
            for hid, bs in rel_by_hole.items():
                if hid.startswith("tau@"):
                    for b in bs:
                        _full_assign[b] = True
                else:
                    for idx_b, b in enumerate(bs):
                        _full_assign[b] = (idx_b == 0)
            _chosen_full = _recover_chosen_atoms(
                problem, system, _full_assign,
            )
            from .lean_backend.codegen import (
                HelperRegistry as _HR, _attach_indices as _ai,
            )
            if isinstance(problem.helper_registry, _HR):
                _entry = problem.helper_registry.find(
                    sc.kind, _loop_id_sc, sc.branch_idx,
                    _ai(problem, _chosen_full),
                )
                if _entry is not None:
                    from pathlib import Path as _P
                    _dd = (_P(problem.dump_lean_failures_dir)
                           if problem.dump_lean_failures_dir else None)
                    _v = verify_class_via_lean(
                        problem, _chosen_full, sc.kind, _loop_id_sc,
                        theorem_name=f"sc{sc_idx}_fallthrough",
                        timeout_s=_adaptive_timeout_s(sc_idx),
                        branch_idx=sc.branch_idx,
                        dump_failures_to=_dd,
                    )
                    if _v.via_helper and _v.is_valid:
                        valid_assignments.append(_full_assign)
                        _general_short_circuit = True

        # Axiom-heavy + soundness-critical: skip Z3 entirely; route
        # ALL attribute classes through Lean (cache fast-path +
        # generic tactic chain).  Z3's quantifier-instantiation
        # heuristic is unreliable for axiom-heavy obligations —
        # both SAT and UNSAT verdicts can be spurious — so we don't
        # rely on it.  Lean dispatches run in parallel (thread pool)
        # since each class is independent.
        _axiom_heavy_lean_path = bool(problem.uninterpreted) or bool(problem.axioms)
        # Coverage at procedure-level has loop_id=None by design (translator
        # handles via `_find_top_level_multibranch_sb`); allow it through.
        _loop_id_gate = (sc.kind == "coverage"
                         or _extract_loop_id(sc) is not None)
        _axiom_heavy_lean_path = (_axiom_heavy_lean_path
                                  and sc.kind in _AXIOM_HEAVY_DISPATCH_KINDS
                                  and _LEAN_AVAILABLE_AT_IMPORT
                                  and lean_available()
                                  and _loop_id_gate
                                  )

        # COST_INVS §2 wiring note: cost-* obligations route through
        # Lean ONLY on UNKNOWN (via _on_unknown's _LEAN_TRANSLATABLE_KINDS
        # check).  Eagerly routing nested cost-decrement through Lean
        # ahead of Z3 was tried and found SLOWER for bubble_sort_cost
        # (Lean startup × N subsets > Z3 NIA total).  Routing only on
        # genuinely-quadratic cost expressions would need additional
        # heuristic gating (cost-atom inspection); deferred to a
        # later slice.

        # Axiom-heavy detection: Z3's quantifier-instantiation
        # heuristic can falsely return SAT (refuted) on obligations
        # that are actually VALID under the user-supplied axioms.
        # When the problem has axioms or UFs, Z3's SAT verdicts on
        # soundness-critical obligations are SUSPECT and must be
        # cross-checked against Lean (full dispatch — cache fast
        # path AND generic-tactic-chain fallback).  Only Z3's UNSAT
        # verdicts on axiom-heavy problems are trusted directly.
        _is_axiom_heavy = bool(problem.uninterpreted) or bool(problem.axioms)

        def _on_z3_sat(
            full_test: dict[z3.BoolRef, bool],
            record_assign: dict[z3.BoolRef, bool],
        ) -> None:
            """Called when Z3 returns SAT (refutation) on a class.

            For axiom-heavy soundness-critical obligations, Z3's
            SAT is unreliable (quantifier instantiation may have
            missed an axiom instance).  Route the obligation to
            Lean — first via the curated companion cache
            (`.solved.lean` overrides → VALID, `.invalid.lean`
            confirms → drop), then via Lean's generic tactic
            chain.  Generic chain UNKNOWN/ERROR → respect
            `potentially_unsound`.

            For non-axiom problems, Z3's SAT is trusted (the class
            is genuinely invalid); drop without further checks.
            """
            nonlocal lean_dispatch_hits, lean_dispatch_misses
            nonlocal lean_dispatch_errors
            nonlocal helper_dispatch_hits, helper_dispatch_misses
            # Ranking obligations (ranking-lb, ranking-decrease) are
            # linear arithmetic over ϕ + loop vars; Z3's SAT verdict
            # IS reliable on these even when the benchmark has UF
            # axioms in scope.  Cross-checking would route to Lean
            # with an empty-τ hardest case, where Lean's `omega`
            # can't prove the goal (no τ premises) — Lean returns
            # ERROR, the class incorrectly lands in
            # unknown_deferred, and the constraint loses a valid
            # rejection.  Trust Z3 directly here.
            if sc.kind in ("ranking-lb", "ranking-decrease",
                           "ranking-proc-lb", "ranking-proc-decrease"):
                return
            # Coverage with sc.loop_id=None is procedure-level
            # SB(n>1) coverage — `theorem_for_coverage` doesn't
            # support this (it looks up the SB via the loop's body).
            # Trust Z3 directly; the disjunction is structurally
            # simple (linear arithmetic on guard atoms).
            # NB: use the RAW `sc.loop_id` here, not
            # `_extract_loop_id(sc)` — the latter falls back to
            # atom_refs and returns the τ atoms' loop_id (e.g. L0),
            # which would defeat the skip.
            if sc.kind == "coverage" and sc.loop_id is None:
                return
            if not (_is_axiom_heavy
                    and sc.kind in _LEAN_TRANSLATABLE_KINDS
                    and _LEAN_AVAILABLE_AT_IMPORT
                    and lean_available()):
                return
            # Wedge-detector: if this constraint has been abandoned,
            # defer immediately without burning Lean time.
            if sc_idx in wedge_abandoned:
                unknown_deferred.append(record_assign)
                return
            chosen = _recover_chosen_atoms(problem, system, full_test)
            loop_id = _extract_loop_id(sc)
            if loop_id is None:
                return
            from pathlib import Path
            dump_dir = (
                Path(problem.dump_lean_failures_dir)
                if problem.dump_lean_failures_dir else None
            )
            v = verify_class_via_lean(
                problem, chosen, sc.kind, loop_id,
                theorem_name=f"sc{sc_idx}_fallthrough",
                timeout_s=_adaptive_timeout_s(sc_idx),
                dump_failures_to=dump_dir,
                branch_idx=sc.branch_idx,
            )
            if v.via_helper:
                helper_dispatch_hits += 1
            else:
                helper_dispatch_misses += 1
            _wedge_track(sc_idx, sc, v.status, dump_dir)
            _maybe_print_progress(sc_idx, sc)
            if v.is_valid:
                valid_assignments.append(record_assign)
                lean_dispatch_hits += 1
                return
            if v.is_invalid:
                # Cached `.invalid.lean` confirms invalidity — drop.
                lean_dispatch_hits += 1
                return
            if v.status == "unknown":
                lean_dispatch_misses += 1
            else:
                lean_dispatch_errors += 1
            # Lean couldn't decide either; defer.  Under sound mode
            # this is effectively a REJECT.
            unknown_deferred.append(record_assign)

        def _on_unknown(
            record_assign: dict[z3.BoolRef, bool],
            full_test: dict[z3.BoolRef, bool] | None = None,
        ) -> None:
            """Record an UNKNOWN check.

            `record_assign` is what we'll store as deferred-or-valid
            (typically `other_assign`).  `full_test` is the full
            indicator assignment that the Z3 check actually saw
            (`{**other_assign, **hardest_free_assign}` for the free-τ
            fast path); if None, defaults to `record_assign`.

            Ring 2: when the obligation is soundness-critical AND
            the Lean toolchain is available, try Lean as a second-
            chance verifier with the full test.  On Lean VALID,
            record as valid (Z3 was the limiting factor, not the
            obligation).  Otherwise defer (which under default
            sound-mode is effectively a REJECT — only under
            `Problem.potentially_unsound = True` are deferred
            classes ever promoted).  See SOUNDNESS.md.
            """
            nonlocal lean_dispatch_hits, lean_dispatch_misses
            nonlocal lean_dispatch_errors
            nonlocal helper_dispatch_hits, helper_dispatch_misses
            if full_test is None:
                full_test = record_assign
            # Lean fallthrough fires whenever the toolchain is
            # available — independent of `potentially_unsound`.  A
            # Lean-VALID class is genuinely valid; we always want
            # to use it.  Only the LENIENT promotion of UNKNOWN-
            # deferred classes is gated on potentially_unsound (per
            # `SOUNDNESS.md`).
            # Wedge-detector: if abandoned, skip Lean and go
            # straight to defer/accept.
            if sc_idx in wedge_abandoned:
                if sc.kind in _REJECT_UNKNOWN_KINDS:
                    unknown_deferred.append(record_assign)
                else:
                    valid_assignments.append(record_assign)
                return
            if (sc.kind in _LEAN_TRANSLATABLE_KINDS
                    and _LEAN_AVAILABLE_AT_IMPORT
                    and lean_available()):
                chosen = _recover_chosen_atoms(problem, system, full_test)
                loop_id = _extract_loop_id(sc)
                if loop_id is not None:
                    from pathlib import Path
                    dump_dir = (
                        Path(problem.dump_lean_failures_dir)
                        if problem.dump_lean_failures_dir else None
                    )
                    # Ranking obligations: cache-only Lean.  These are
                    # linear arithmetic where Z3 UNKNOWN typically means
                    # a τ subset is missing load-bearing atoms.  Lean's
                    # generic tactic chain can't recover those without
                    # τ premises Z3 also lacked — burns 5-15s per call.
                    # But a curated `.solved.lean` companion CAN recover
                    # specific subsets (UF axiom orchestration Lean does
                    # better).  Consult the cache only, skip generic
                    # tactic chain.  See RESEARCH.LEAN.md §9.
                    _ranking_kind = sc.kind in (
                        "ranking-lb", "ranking-decrease",
                        "ranking-proc-lb", "ranking-proc-decrease",
                    )
                    v = verify_class_via_lean(
                        problem, chosen, sc.kind, loop_id,
                        theorem_name=f"sc{sc_idx}_fallthrough",
                        timeout_s=_adaptive_timeout_s(sc_idx),
                        dump_failures_to=dump_dir,
                        cache_only=_ranking_kind,
                    )
                    if v.via_helper:
                        helper_dispatch_hits += 1
                    else:
                        helper_dispatch_misses += 1
                    _wedge_track(sc_idx, sc, v.status, dump_dir)
                    _maybe_print_progress(sc_idx, sc)
                    if v.is_valid:
                        valid_assignments.append(record_assign)
                        lean_dispatch_hits += 1
                        return
                    if v.is_invalid:
                        # Curated `.invalid.lean` proves this τ subset
                        # is genuinely unprovable (existential
                        # counterexample type-checked).  Reject
                        # certainly — do NOT add to unknown_deferred,
                        # so lenient mode can't accept it.
                        lean_dispatch_hits += 1
                        return
                    if v.status == "unknown":
                        lean_dispatch_misses += 1
                    else:
                        lean_dispatch_errors += 1
            if sc.kind in _REJECT_UNKNOWN_KINDS:
                unknown_deferred.append(record_assign)
            else:
                valid_assignments.append(record_assign)

        if _axiom_heavy_lean_path:
            # Enumerate (other-hole × free-τ) combinations and
            # dispatch to Lean in parallel.  Phase 3.L monotonicity
            # fast-path: for each `other_assign`, try the
            # `hardest_free_assign` FIRST in one dispatch.  If Lean
            # validates it, the conjunctive τ structural argument
            # says all 2^|free-τ| subsets are also valid (ANT-only
            # → upward monotone; CONS-only → downward monotone).
            # We record an "abridged" assignment that omits the
            # free-τ indicators (leaving them unconstrained in the
            # main SAT).  Only if the hardest case fails do we fall
            # back to per-subset enumeration of the free-τ holes.
            #
            # Monotonicity is a STRUCTURAL property of conjunctive
            # τ; it doesn't depend on the verifier (Z3 or Lean).
            # The earlier comment "Z3 verdicts aren't trusted so
            # we can't short-circuit" conflated trust in verdicts
            # with trust in monotonicity.  Lean verdicts are
            # equally sound for monotonicity-fast-path use.
            from pathlib import Path
            dump_dir = (
                Path(problem.dump_lean_failures_dir)
                if problem.dump_lean_failures_dir else None
            )
            loop_id = _extract_loop_id(sc)
            # Coverage at procedure-level passes loop_id=None to the
            # translator (which dispatches via _find_top_level_multibranch_sb).
            assert loop_id is not None or sc.kind == "coverage"
            theorem_name = f"sc{sc_idx}_fallthrough"

            sc_branch_idx = sc.branch_idx
            def _dispatch(full_assign: dict[z3.BoolRef, bool]):
                chosen = _recover_chosen_atoms(
                    problem, system, full_assign,
                )
                return verify_class_via_lean(
                    problem, chosen, sc.kind, loop_id,
                    theorem_name=theorem_name,
                    timeout_s=_adaptive_timeout_s(sc_idx),
                    branch_idx=sc_branch_idx,
                    dump_failures_to=dump_dir,
                )

            def _record_dispatch_result(v, rec):
                """Update counters + valid/deferred lists for one v."""
                if v.via_helper:
                    helper_dispatch_hits_local[0] += 1
                else:
                    helper_dispatch_misses_local[0] += 1
                _wedge_track(sc_idx, sc, v.status, dump_dir)
                _maybe_print_progress(sc_idx, sc)
                if v.is_valid:
                    valid_assignments.append(rec)
                    lean_hits_local[0] += 1
                elif v.is_invalid:
                    lean_hits_local[0] += 1
                elif v.status == "unknown":
                    lean_misses_local[0] += 1
                    unknown_deferred.append(rec)
                else:  # error
                    lean_errs_local[0] += 1
                    unknown_deferred.append(rec)

            # Mutable counters (closure-captured); fold into the
            # outer dispatch totals after enumeration.
            lean_hits_local = [0]
            lean_misses_local = [0]
            lean_errs_local = [0]
            helper_dispatch_hits_local = [0]
            helper_dispatch_misses_local = [0]

            # §H.2 helper short-circuit (RESEARCH.md §H.2.CODEGEN).
            # Before enumerating 2^|τ| subsets, check if a Tier-3
            # helper covers the FULL τ subset.  If yes, dispatch
            # ONCE; on VALID, add the full-τ cube to the constraint
            # and SKIP per-subset enumeration entirely.
            #
            # Soundness: each cube emitted is a valid attribute
            # class proved by the helper.  We do NOT generalize
            # "helper valid for full τ" to "all subsets valid"
            # (that's the unsound H.2.PROTOTYPE direction); we just
            # add the one cube the helper actually proves.
            #
            # Completeness tradeoff: smaller τ subsets that ALSO
            # would have validated (via generic chain or another
            # helper) are skipped.  Means the synthesizer's chosen
            # subset for this constraint will be the FULL τ — score
            # not minimized.  For benchmarks where E2E tractability
            # matters more than score-minimization (axiom-heavy
            # constraints) this is the right tradeoff.  Per-atom
            # helpers (task #170) restore score-minimization later.
            short_circuit_fired = False
            if problem.helper_registry is not None:
                # Build the full-τ assignment: for each hole that
                # appears in this constraint's body, pick:
                #   - τ holes: ALL atoms True (the full subset).
                #   - non-τ holes: the first single-hot option.
                full_assign: dict[z3.BoolRef, bool] = {}
                for hid, bs in rel_by_hole.items():
                    if hid.startswith("tau@"):
                        for b in bs:
                            full_assign[b] = True
                    else:
                        # Single-hot: first option True, rest False.
                        for idx_b, b in enumerate(bs):
                            full_assign[b] = (idx_b == 0)
                # Match-check against the registry: chosen_atoms for
                # this full assignment must satisfy the helper's
                # required_atoms predicate.
                chosen_full = _recover_chosen_atoms(
                    problem, system, full_assign,
                )
                from .lean_backend.codegen import (
                    HelperRegistry, _attach_indices,
                )
                if isinstance(problem.helper_registry, HelperRegistry):
                    entry = problem.helper_registry.find(
                        sc.kind, loop_id, sc.branch_idx,
                        _attach_indices(problem, chosen_full),
                    )
                    if entry is not None:
                        # Dispatch once.  If valid, emit ONLY the
                        # full-τ cube.
                        v = _dispatch(full_assign)
                        total_checks += 1
                        if v.via_helper:
                            helper_dispatch_hits_local[0] += 1
                        else:
                            helper_dispatch_misses_local[0] += 1
                        _wedge_track(sc_idx, sc, v.status, dump_dir)
                        _maybe_print_progress(sc_idx, sc)
                        if v.is_valid:
                            valid_assignments.append(full_assign)
                            lean_hits_local[0] += 1
                            short_circuit_fired = True

            # If the helper short-circuit didn't fire, fall through
            # to Phase A (hardest case) + Phase B (per-subset
            # fallback).  If it did fire, the cube is already in
            # valid_assignments and we skip enumeration entirely.
            if not short_circuit_fired:
                # Phase A: hardest-case dispatch per `other_assign`.
                # Each succeeds → record abridged cube (free-τ
                # unconstrained).  Each fails → schedule per-subset
                # enumeration for that combo in Phase B.
                hardest_work: list[tuple[dict, dict]] = []
                for combo in product(*per_hole_assignments):
                    other_assign: dict[z3.BoolRef, bool] = {}
                    for ha in combo:
                        other_assign.update(ha)
                    if free_taus:
                        full_assign = {**other_assign, **hardest_free_assign}
                        # Record `other_assign` only — free-τ omitted on
                        # success.  On fallback we'll record per-subset.
                        hardest_work.append((full_assign, other_assign))
                    else:
                        hardest_work.append((other_assign, other_assign))

                # Track which other_assigns need Phase B fallback.
                fallback_other_assigns: list[dict] = []
                with ThreadPoolExecutor(
                    max_workers=_LEAN_PARALLEL_WORKERS
                ) as ex:
                    futures = {
                        ex.submit(_dispatch, full): (full, rec)
                        for full, rec in hardest_work
                    }
                    for fut in as_completed(futures):
                        if sc_idx in wedge_abandoned:
                            # Cancel queued futures; in-flight ones
                            # (≤ workers) still drain.
                            ex.shutdown(wait=False, cancel_futures=True)
                            break
                        full, rec = futures[fut]
                        v = fut.result()
                        total_checks += 1
                        if v.via_helper:
                            helper_dispatch_hits_local[0] += 1
                        else:
                            helper_dispatch_misses_local[0] += 1
                        _wedge_track(sc_idx, sc, v.status, dump_dir)
                        _maybe_print_progress(sc_idx, sc)
                        if v.is_valid:
                            # Hardest case validates → record abridged
                            # cube.  All free-τ subsets covered.
                            valid_assignments.append(rec)
                            lean_hits_local[0] += 1
                        elif v.is_invalid:
                            # Hardest case is unprovable; for free-τ
                            # holes this is conservative — we still
                            # enumerate subsets in case some subset IS
                            # provable.  For non-free-τ, drop.
                            if free_taus:
                                fallback_other_assigns.append(rec)
                            else:
                                lean_hits_local[0] += 1
                        elif v.status == "unknown":
                            if free_taus:
                                fallback_other_assigns.append(rec)
                            else:
                                lean_misses_local[0] += 1
                                unknown_deferred.append(rec)
                        else:  # error
                            if free_taus:
                                fallback_other_assigns.append(rec)
                            else:
                                lean_errs_local[0] += 1
                                unknown_deferred.append(rec)

                # Phase B: per-subset fallback for `other_assign`s
                # where the hardest case didn't validate.  Only fires
                # when there's a free-τ hole AND the hardest case
                # didn't close — likely BOTH-position atoms in practice
                # (which would have been classified as `other_holes`,
                # not free_taus — so this fallback is usually empty).
                if (fallback_other_assigns and free_taus
                        and sc_idx not in wedge_abandoned):
                    fb_work: list[tuple[dict, dict]] = []
                    for other_assign in fallback_other_assigns:
                        for free_combo in product(*free_tau_subset_options):
                            free_assign: dict[z3.BoolRef, bool] = {}
                            for fa in free_combo:
                                free_assign.update(fa)
                            # Skip the hardest case (already tried).
                            if free_assign == hardest_free_assign:
                                continue
                            full = {**other_assign, **free_assign}
                            fb_work.append((full, full))

                    with ThreadPoolExecutor(
                        max_workers=_LEAN_PARALLEL_WORKERS
                    ) as ex:
                        futures = {
                            ex.submit(_dispatch, full): (full, rec)
                            for full, rec in fb_work
                        }
                        for fut in as_completed(futures):
                            if sc_idx in wedge_abandoned:
                                ex.shutdown(wait=False, cancel_futures=True)
                                break
                            full, rec = futures[fut]
                            v = fut.result()
                            total_checks += 1
                            _record_dispatch_result(v, rec)

            # Fold local counters into the outer totals (both
            # short-circuit and Phase A/B paths use these).
            lean_dispatch_hits += lean_hits_local[0]
            lean_dispatch_misses += lean_misses_local[0]
            lean_dispatch_errors += lean_errs_local[0]
            helper_dispatch_hits += helper_dispatch_hits_local[0]
            helper_dispatch_misses += helper_dispatch_misses_local[0]

            # Skip the Z3 enumeration loop below — axiom-heavy path
            # owns this constraint's class enumeration.
            assignments_done = True
        else:
            assignments_done = False

        # ── Unsat-core-inspired fast path (RESEARCH.md §H.2) ──
        # PROTOTYPE BANKED — does NOT compose with BOTH-position
        # distractor atoms.  Hard-disabled until a future iteration
        # addresses the caveats banked in RESEARCH.md §H.2.PROTOTYPE.
        #
        # ⚠️  DO NOT just flip this flag to True.  ⚠️
        # The fast-path body (when re-enabled) was found UNSOUND on
        # intsqrt because:
        #
        #  (1) "All-True τ" is the HARDEST case for BOTH-position
        #      atoms with distractors (e.g., intsqrt's `v >= x` and
        #      `i == 1` don't preserve under the transition).  Z3
        #      returns SAT (refuted) for the all-True check, so the
        #      fast path misses the non-vacuous valid configs
        #      (3 real invariants True, 2 distractors False).
        #
        #  (2) Vacuous-by-guard-contradiction cases (e.g., guard
        #      `v<x` + τ atom `v >= x`) survive the filtered
        #      enumeration with empty unsat-core and produce cubes
        #      that admit unsound programs.
        #
        #  (3) Z3's `solver.check(assumptions)` was state-sensitive
        #      on the cached `verifier` — the assumption-mode check
        #      diverged from substitution-mode on the same body.
        #      A fresh `z3.Solver()` per check was required.
        #
        # The infrastructure (both_tau_hole_indices, sh_hole_indices,
        # all_true_both_tau above) is preserved as the starting
        # point for the next iteration.  Plausible next moves
        # (RESEARCH.md §H.2.PROTOTYPE):
        #
        #  - Bottom-up enumeration with unsat cores: try empty τ
        #    first, add atoms incrementally.
        #  - Z3 native ALL-SAT mode on parameterized τ indicators.
        #  - `(set-option :smt.core.minimize true)` for tighter
        #    cores.
        #  - Pivot to §H.1 (Tier-3 helpers + content-pattern cache),
        #    which attacks per-class Lean dispatch cost — likely the
        #    bigger lever for axiom-heavy benchmarks.
        #
        # If you re-enable this, run the regression suite first
        # (especially intsqrt — historically the canary for this
        # class of bug) and check that solution counts match.
        _fast_path_enabled = False  # disabled — see RESEARCH.md §H.2.PROTOTYPE
        _fast_path_hit = False

        for combo in (() if (assignments_done or _general_short_circuit)
                      else product(*per_hole_assignments)):
            other_assign: dict[z3.BoolRef, bool] = {}
            for hole_assign in combo:
                other_assign.update(hole_assign)

            if free_taus:
                # Try the hardest free-τ assignment first.
                test = {**other_assign, **hardest_free_assign}
                subs = [(b, z3.BoolVal(v)) for b, v in test.items()]
                concrete = z3.substitute(sc.body, *subs)
                n_checks, vr = _check_validity(concrete, verifier)
                total_checks += n_checks
                if vr == z3.unsat:
                    # Hardest passes ⇒ every free-τ subset passes for
                    # this `other_assign`.  Emit cube without free-τ
                    # literals.
                    valid_assignments.append(other_assign)
                    free_tau_hits += 1
                    continue
                if vr == z3.unknown:
                    _record_unknown(sc_idx, sc)
                    _on_unknown(other_assign, full_test=test)
                    if sc.kind not in _REJECT_UNKNOWN_KINDS:
                        free_tau_hits += 1
                    continue
                # vr == z3.sat (refuted) on the hardest free-τ
                # assignment.  For axiom-heavy problems, consult the
                # curated cache before falling back to per-subset
                # enumeration — Z3 may have spuriously refuted the
                # hardest case.
                _on_z3_sat(test, other_assign)
                # Hardest failed; fall back to enumerating free-τ
                # subsets.
                free_tau_misses += 1

                # EXPERIMENTAL (RESEARCH.md §experimental_cardinality):
                # cardinality-ordered enumeration with monotone pruning.
                # For ANT-only free τ (pos=False), validity is monotone-
                # UPWARD: if subset S is valid, every superset of S is
                # also valid.  Enumerate by ASCENDING |S|, stop at first
                # valid → all supersets implicitly valid by structure.
                # Symmetric for CONS-only (pos=True): monotone-DOWNWARD,
                # enumerate by DESCENDING |S|, stop at first valid.
                #
                # Only safe when ALL free_taus share the same position
                # (otherwise joint monotonicity isn't clean).
                _positions = {pos for _, _, pos in free_taus}
                _ant_only = (_positions == {False})
                _cons_only = (_positions == {True})
                # Gate on |τ| ≥ 10.  Below this, original 2^N
                # enumeration is fast (Z3 amortizes well across
                # similar subsets via push/pop).  Above, the
                # exponential dominates and cardinality wins.
                # Threshold tuned: FW's sc10 has 18 atoms (huge
                # win); sum_array's sc?-rank has 7 atoms (loses
                # because each Z3 check is dominated by UF
                # E-matching overhead, not subset count).
                _flat_count = sum(len(bs) for _, bs, _ in free_taus)
                _cardinality_path = (
                    (_ant_only or _cons_only)
                    and sc.kind in ("ranking-lb", "ranking-decrease",
                                    "ranking-proc-lb",
                                    "ranking-proc-decrease")
                    and _flat_count >= 10
                )

                if _cardinality_path:
                    # Flatten free-τ indicators into one list with
                    # per-hole index ranges so we can iterate over
                    # subsets of the joint atom set.
                    flat_indicators: list[z3.BoolRef] = []
                    for _, bs, _ in free_taus:
                        flat_indicators.extend(bs)
                    n_flat = len(flat_indicators)
                    # Ascending for ANT, descending for CONS.
                    if _ant_only:
                        size_iter = range(1, n_flat + 1)  # skip empty (already failed)
                    else:
                        size_iter = range(n_flat - 1, -1, -1)  # skip full (already failed)
                    found_minimal = False
                    for k in size_iter:
                        if found_minimal:
                            break
                        for sub in itertools.combinations(
                                range(n_flat), k):
                            sub_set = set(sub)
                            # ANT: in-subset = True (atom present);
                            # CONS: in-subset = True (atom present),
                            # complement = False — same encoding.
                            free_assign = {
                                b: (i_ in sub_set)
                                for i_, b in enumerate(flat_indicators)
                            }
                            test = {**other_assign, **free_assign}
                            subs = [(b, z3.BoolVal(v))
                                    for b, v in test.items()]
                            concrete = z3.substitute(sc.body, *subs)
                            n_checks, vr = _check_validity(
                                concrete, verifier)
                            total_checks += n_checks
                            if vr == z3.unsat:
                                # Minimal valid found.  Encode the cube
                                # to ENFORCE only the minimal atoms;
                                # leave others FREE so the main SAT
                                # can pick supersets too (sound by
                                # monotonicity).
                                #   ANT-only: minimal atoms must be
                                #     True; free atoms can be True/False.
                                #   CONS-only: minimal atoms must be
                                #     True (still "more atoms" in
                                #     consequent for our convention);
                                #     wait — for CONS-only "smaller"
                                #     means FEWER consequent atoms.
                                #     The hardest = full; minimal valid
                                #     = the smallest set of consequent
                                #     atoms that's provable.
                                #
                                # For ANT-only: include only the True
                                # indicators in the cube assignment.
                                # For CONS-only: include only the FALSE
                                # indicators (they're "absence of atoms"
                                # which is required for the smaller
                                # subset).
                                minimal_cube: dict[z3.BoolRef, bool] = {
                                    b: v for b, v in other_assign.items()
                                }
                                for b, v in free_assign.items():
                                    # ANT-only & v=True → required.
                                    # CONS-only & v=False → required
                                    # (atom absent → must stay absent).
                                    if (_ant_only and v) or (_cons_only and not v):
                                        minimal_cube[b] = v
                                valid_assignments.append(minimal_cube)
                                found_minimal = True
                                break
                            elif vr == z3.unknown:
                                _record_unknown(sc_idx, sc)
                                _on_unknown(test)
                            # vr == sat: keep enumerating.
                    # If no minimal valid found at any cardinality:
                    # the constraint is fully infeasible for this
                    # `other_assign` — no cube added.
                else:
                    # Original enumeration: try all 2^N subsets.
                    for free_combo in product(*free_tau_subset_options):
                        free_assign: dict[z3.BoolRef, bool] = {}
                        for fa in free_combo:
                            free_assign.update(fa)
                        if free_assign == hardest_free_assign:
                            continue  # already failed
                        test = {**other_assign, **free_assign}
                        subs = [(b, z3.BoolVal(v))
                                for b, v in test.items()]
                        concrete = z3.substitute(sc.body, *subs)
                        n_checks, vr = _check_validity(concrete, verifier)
                        total_checks += n_checks
                        if vr == z3.unsat:
                            valid_assignments.append(test)
                        elif vr == z3.unknown:
                            _record_unknown(sc_idx, sc)
                            _on_unknown(test)
                        else:  # z3.sat
                            _on_z3_sat(test, test)
            else:
                subs = [(b, z3.BoolVal(v)) for b, v in other_assign.items()]
                concrete = z3.substitute(sc.body, *subs)
                n_checks, vr = _check_validity(concrete, verifier)
                total_checks += n_checks
                if vr == z3.unsat:
                    valid_assignments.append(other_assign)
                elif vr == z3.unknown:
                    _record_unknown(sc_idx, sc)
                    _on_unknown(other_assign)
                else:  # z3.sat
                    _on_z3_sat(other_assign, other_assign)

        # Sound-mode rule: unknown_deferred classes are NEVER
        # promoted.  The `potentially_unsound` field on Problem
        # remains as a developer escape hatch (no committed
        # benchmark uses it) but its solver-level promotion paths
        # were excised after factorial / fib / sum_array /
        # array_product / count_zeros all became sound by default
        # via the chain-bundle Lean translator + curated
        # `.solved.lean`.  See SOUNDNESS.md.

        if (not valid_assignments and not unknown_deferred
                and sc_idx not in wedge_abandoned):
            elapsed = time.monotonic() - start
            return NoSolution(
                reason="unsat",
                unsat_core=[],
                hints=[
                    f"Safety constraint #{sc_idx} ({sc.kind}) has no valid "
                    f"attribute class — predicate space lacks the atoms "
                    f"needed.  Enumerated {total_checks} candidates in "
                    f"{elapsed:.1f}s."
                ] + _lean_dispatch_hint_lines(
                    lean_dispatch_hits, lean_dispatch_misses,
                    lean_dispatch_errors,
                ) + _helper_coverage_hint_lines(
                    helper_dispatch_hits, helper_dispatch_misses
                ),
                lean_dispatch=LeanDispatchStats(
                    valid=lean_dispatch_hits,
                    unknown=lean_dispatch_misses,
                    errors=lean_dispatch_errors,
                ),
            )

        # Encode this constraint's valid classes as a disjunction-of-cubes.
        # Phase 3.L fast path can produce empty `assign` dicts when
        # every relevant indicator was in a free-τ hole and the
        # hardest case validated — the cube becomes "any assignment"
        # (BoolVal True).  If ANY cube is True, the whole clause is
        # True and we can skip adding it altogether.
        def _to_cube(assignment: dict[z3.BoolRef, bool]) -> z3.ExprRef | None:
            if not assignment:
                return None  # universal cube
            literals = [b if v else z3.Not(b) for b, v in assignment.items()]
            return z3.And(*literals) if len(literals) > 1 else literals[0]

        strict_cubes: list[z3.ExprRef] = []
        deferred_cubes: list[z3.ExprRef] = []
        skip_clause = False
        for assign in valid_assignments:
            c = _to_cube(assign)
            if c is None:
                skip_clause = True
                break
            strict_cubes.append(c)
        if not skip_clause:
            for assign in unknown_deferred:
                c = _to_cube(assign)
                if c is None:
                    skip_clause = True
                    break
                deferred_cubes.append(c)
        if skip_clause:
            per_constraint_cubes.append(([], []))  # universal — no clause
            continue
        per_constraint_cubes.append((strict_cubes, deferred_cubes))
        if os.environ.get("SYNTH_DEBUG_CUBES"):
            print(f"  [DEBUG] sc{sc_idx} kind={sc.kind!r} loop={sc.loop_id!r} "
                  f"branch={sc.branch_idx}: "
                  f"{len(strict_cubes)} strict + {len(deferred_cubes)} deferred cubes",
                  flush=True)

    enumeration_elapsed = time.monotonic() - start

    # ── Step 3+4: Boolean SAT for indicator assignment. ──────────────
    def _build_clauses() -> list[z3.ExprRef]:
        out: list[z3.ExprRef] = []
        for strict_cubes, deferred_cubes in per_constraint_cubes:
            if not strict_cubes and not deferred_cubes:
                continue  # universal cube, no clause needed
            cubes = strict_cubes  # deferred cubes never promoted now
            if not cubes:
                # No confirmed-valid cubes → this constraint is
                # unsatisfiable.  Defensive: clause = False.
                out.append(z3.BoolVal(False))
            else:
                out.append(z3.Or(*cubes) if len(cubes) > 1 else cubes[0])
        return out

    def _run_main(clauses: list[z3.ExprRef]) -> tuple[list[Solution], z3.CheckSatResult]:
        m = z3.Solver()
        if problem.solver_timeout_ms > 0:
            m.set("timeout", problem.solver_timeout_ms)
        for a in system.well_form:
            m.add(a)
        for c in clauses:
            m.add(c)
        sols: list[Solution] = []
        last = z3.sat
        while len(sols) < problem.max_solutions:
            last = m.check()
            if last == z3.unsat or last == z3.unknown:
                break
            sols.append(decode(m.model(), problem, scaffold, system))
            m.add(_blocker(m.model(), all_indicators))
        return sols, last

    solutions, last_result = _run_main(_build_clauses())
    # The global lenient fallback that previously promoted
    # unknown_deferred cubes when `potentially_unsound = True`
    # was excised — no committed benchmark requires it, and the
    # chain-bundle Lean translator + `.solved.lean` cache now
    # cover the formerly-deferred axiom-heavy obligations.

    lean_stats = LeanDispatchStats(
        valid=lean_dispatch_hits,
        unknown=lean_dispatch_misses,
        errors=lean_dispatch_errors,
    )

    if last_result == z3.unknown:
        return Timeout(
            reason="timeout",
            budget_seconds=problem.solver_timeout_ms / 1000.0,
            hole_sizes=system.hole_sizes,
            partial_solutions=_score_and_sort(solutions),
            hints=[
                f"main SAT solver returned unknown after enumeration "
                f"of {total_checks} attribute-class checks "
                f"({enumeration_elapsed:.1f}s).  Free-τ fast-path "
                f"hits/misses: {free_tau_hits}/{free_tau_misses}."
            ] + _lean_dispatch_hint_lines(
                lean_dispatch_hits, lean_dispatch_misses,
                lean_dispatch_errors
            ) + _helper_coverage_hint_lines(
                helper_dispatch_hits, helper_dispatch_misses
            ),
            lean_dispatch=lean_stats,
        )

    if not solutions:
        _wedge_hints: list[str] = []
        if wedge_abandoned:
            _wedge_hints.append(
                f"NEEDS-HELPERS: {len(wedge_abandoned)} constraint(s) "
                f"wedged on Lean dispatch and were abandoned.  Write a "
                f"Tier-3 helper for each, or raise "
                f"`Problem.wedge_threshold` if more dispatches are "
                f"genuinely needed."
            )
            for _sci in sorted(wedge_abandoned):
                _d = wedge_details[_sci]
                _line = (f"  - sc{_sci}: kind={_d['kind']}, "
                         f"loop_id={_d['loop_id']}, "
                         f"branch_idx={_d['branch_idx']}, "
                         f"{_d['dispatches']} dispatches")
                if _d["dump_dir"]:
                    _line += (f" — see {_d['dump_dir']}/"
                              f"sc{_sci}_fallthrough_*.failed.lean")
                _wedge_hints.append(_line)
        return NoSolution(
            reason=("needs-helpers" if wedge_abandoned else "unsat"),
            unsat_core=[],
            hints=_wedge_hints + [
                f"valid attribute classes per constraint were found, but "
                f"no Boolean assignment satisfies all of them simultaneously "
                f"(after {total_checks} attribute-class checks, "
                f"{enumeration_elapsed:.1f}s).",
            ]
            + _unknown_localization_hint_lines(
                unknown_checks, unknown_details
            )
            + _lean_dispatch_hint_lines(
                lean_dispatch_hits, lean_dispatch_misses,
                lean_dispatch_errors
            ) + _helper_coverage_hint_lines(
                helper_dispatch_hits, helper_dispatch_misses
            ),
            lean_dispatch=lean_stats,
        )

    return SolveResult(
        solutions=_score_and_sort(solutions),
        hints=_lean_dispatch_hint_lines(
            lean_dispatch_hits, lean_dispatch_misses,
            lean_dispatch_errors
        ) + _helper_coverage_hint_lines(
            helper_dispatch_hits, helper_dispatch_misses
        ),
        lean_dispatch=lean_stats,
    )


# ─────────────────────────────────────────────────────────────────────
# Helpers.
# ─────────────────────────────────────────────────────────────────────
def _check_validity(body: z3.ExprRef,
                    verifier: z3.Solver) -> tuple[int, z3.CheckSatResult]:
    """Z3-check whether `axioms ⇒ body` is valid by SAT-checking the
    negation.  Uses push/pop on a shared verifier solver that already
    has axioms asserted.  Returns (1, result) — the integer mirrors a
    future API where one call might do multiple Z3 queries."""
    verifier.push()
    verifier.add(z3.Not(body))
    r = verifier.check()
    verifier.pop()
    return 1, r


def _classify_atoms(sc: SafetyConstraint) -> dict[tuple[str, int], set[bool]]:
    """For each (hole_id, atom_idx) appearing in `sc.atom_refs`, return
    the set of `is_consequent` values it was tagged with.  The size of
    the set tells us the atom's monotonicity class within this
    constraint:

        {False}      — ANT-only   (validity monotone-upward in subset)
        {True}       — CONS-only  (validity monotone-downward in subset)
        {False, True} — BOTH       (no monotonicity guarantee)
    """
    cls: dict[tuple[str, int], set[bool]] = {}
    for ref in sc.atom_refs:
        cls.setdefault((ref.hole_id, ref.atom_idx), set()).add(ref.is_consequent)
    return cls


def _free_tau_position(hid: str,
                       bs: list[z3.BoolRef],
                       classification: dict[tuple[str, int], set[bool]]
                       ) -> bool | None:
    """Return the single shared position for a τ hole's in-body atoms,
    or None if the hole is not τ / has mixed positions / has atoms
    without classification info.

    A return of `True` means all in-body atoms are CONS-only (validity
    is monotone-downward: try the full set first).  `False` means
    ANT-only (validity is monotone-upward: try the empty set first).
    """
    if not hid.startswith("tau@"):
        return None
    positions: set[bool] = set()
    # Each indicator b in `bs` is `b__tau@LX__k`; recover the atom_idx
    # from the suffix.  The convention is set in constraints.py
    # (`z3.Bool(f"b__{hole.id}__{k}")`).
    for b in bs:
        name = str(b)
        try:
            idx = int(name.rsplit("__", 1)[1])
        except (ValueError, IndexError):
            return None
        pos = classification.get((hid, idx), None)
        if pos is None or len(pos) != 1:
            return None
        positions.update(pos)
        if len(positions) > 1:
            return None
    if len(positions) != 1:
        return None
    return positions.pop()


def _collect_relevant(expr: z3.ExprRef,
                      indicator_id_set: set[int],
                      all_indicators: list[z3.BoolRef]) -> list[z3.BoolRef]:
    """Walk `expr` and return the indicator booleans that occur in it.

    `indicator_id_set` is the set of Z3 expr-ids identifying indicators;
    `all_indicators` is a flat list used to resolve ids back to refs.
    """
    id_to_ref = {b.get_id(): b for b in all_indicators}
    found: list[z3.BoolRef] = []
    seen_ids: set[int] = set()
    seen_returned: set[int] = set()
    stack = [expr]
    while stack:
        e = stack.pop()
        eid = e.get_id()
        if eid in seen_ids:
            continue
        seen_ids.add(eid)
        if eid in indicator_id_set:
            if eid not in seen_returned:
                found.append(id_to_ref[eid])
                seen_returned.add(eid)
            continue
        for c in e.children():
            stack.append(c)
    return found


def _blocker(model: z3.ModelRef,
             indicators: list[z3.BoolRef]) -> z3.ExprRef:
    """`⋁ b_k ≠ model[b_k]` — at least one indicator differs.  Used
    only to enumerate additional solutions; not for correctness."""
    parts: list[z3.ExprRef] = []
    for b in indicators:
        v = model.eval(b, model_completion=True)
        parts.append(z3.Not(b) if z3.is_true(v) else b)
    return z3.Or(parts) if len(parts) > 1 else parts[0]


def _score_and_sort(sols: list[Solution]) -> list[Solution]:
    return sorted(sols, key=lambda s: s.score)


def _lean_dispatch_hint_lines(hits: int, misses: int,
                              errors: int) -> list[str]:
    """Telemetry hint lines for the Lean-fallthrough path."""
    if hits == 0 and misses == 0 and errors == 0:
        return []
    return [
        f"Lean fallthrough: {hits} valid, {misses} unknown, "
        f"{errors} error (out of {hits + misses + errors} calls)."
    ]


def _unknown_localization_hint_lines(
    unknown_checks: int,
    unknown_details: dict[int, dict],
) -> list[str]:
    """F18 hint lines: name the top constraints that returned
    UNKNOWN, instead of the old un-localized "1 attribute-class
    returned 'unknown' and were rejected" hint.

    Shows up to 5 sc_idx entries sorted by UNKNOWN count
    (descending), with kind / loop_id / branch_idx — the same
    surface the WEDGE warning uses, so an author can pivot
    straight to the dump dir for that sc.
    """
    if not unknown_checks:
        return []
    if not unknown_details:
        # Pre-F18 fallback in case the per-sc tracking missed
        # an increment site.  Keeps the old hint shape.
        return [
            f"{unknown_checks} attribute-class check(s) returned "
            f"'unknown' and were rejected under sound mode."
        ]
    sorted_scs = sorted(
        unknown_details.items(),
        key=lambda kv: kv[1]["count"],
        reverse=True,
    )
    lines = [
        f"{unknown_checks} attribute-class check(s) returned "
        f"'unknown' and were rejected under sound mode.  "
        f"Top {min(5, len(sorted_scs))} blocking constraint(s):"
    ]
    for sc_idx, info in sorted_scs[:5]:
        lines.append(
            f"  - sc{sc_idx}: {info['count']} UNKNOWN(s), "
            f"kind={info['kind']}, "
            f"loop_id={info['loop_id']}, "
            f"branch_idx={info['branch_idx']}"
        )
    return lines


def _helper_coverage_hint_lines(helper_hits: int,
                                helper_misses: int) -> list[str]:
    """Telemetry hint lines for the §H.2 codegen helper-citation path.

    Shows how many Lean dispatches were absorbed by Tier-3 helpers
    (fast ~2s `exact <helper>` citations) vs ran the generic
    tactic chain (slow ~30-60s).  Coverage ratio is the headline
    metric for whether the codegen is paying off for this benchmark.
    """
    total = helper_hits + helper_misses
    if total == 0:
        return []
    pct = 100.0 * helper_hits / total
    return [
        f"Helper coverage: {helper_hits}/{total} dispatches via "
        f"Tier-3 helper ({pct:.1f}%); "
        f"{helper_misses} fell through to generic tactic chain."
    ]


# ─────────────────────────────────────────────────────────────────────
# Ring 2: Lean-fallthrough helpers.
# ─────────────────────────────────────────────────────────────────────
def _recover_chosen_atoms(problem: Problem,
                          system: Any,
                          assign: dict[z3.BoolRef, bool]) -> dict:
    """Reverse-map an indicator-Boolean assignment to a chosen-atoms
    dict (the same shape `Solution.atoms` would carry).

    Strategy: start from defaults (first candidate of each hole),
    override with whatever `assign` decides for indicators it
    constrains.  For τ holes (conjunctive), collect every atom_idx
    whose indicator maps to True.  For other holes (single-hot), pick
    the unique True one.

    Holes the assignment doesn't touch (because they don't appear in
    the constraint's body) get the first candidate as default.  The
    theorem builders only read what they need, so defaults for
    irrelevant holes are harmless.
    """
    chosen: dict[str, Any] = {}
    # Defaults from problem.atoms.
    for hole_id, candidates in problem.atoms.items():
        if not candidates:
            continue
        if hole_id.startswith("tau@"):
            chosen[hole_id] = list(candidates)  # default: all τ atoms
        else:
            chosen[hole_id] = candidates[0]
    # Overrides from the indicator assignment.
    for hole_id, indicators in system.indicators.items():
        atoms = problem.atoms.get(hole_id, [])
        if hole_id.startswith("tau@"):
            true_idxs = [i for i, b in enumerate(indicators)
                         if assign.get(b, False)]
            # If assign mentions ANY indicator for this hole, trust
            # the assignment exactly (even if the result is the empty
            # τ subset — that's a valid attribute class).
            if any(b in assign for b in indicators):
                chosen[hole_id] = [atoms[i] for i in true_idxs]
        else:
            for i, b in enumerate(indicators):
                if assign.get(b, False):
                    chosen[hole_id] = atoms[i]
                    break
    return chosen


def _extract_loop_id(sc: SafetyConstraint) -> str | None:
    """Return the loop_id this constraint belongs to.

    Constraints emitted by `emit_loop_*` set `sc.loop_id`
    explicitly.  Older constraints (or per-procedure ranking
    constraints not tied to a single loop) have `loop_id = None`;
    fall back to inspecting atom_refs for a `tau@<id>` hint, so
    safety constraints whose loop_id was inherited via atom-ref
    inspection still work.

    EXCEPTION: `coverage` constraints don't follow the fallback.
    For coverage, sc.loop_id semantically means "the loop whose
    body is the multi-branch SB this coverage check is for".
    A coverage with `sc.loop_id is None` is a PROCEDURE-LEVEL
    SB(n>1) coverage (translator handles via
    `_find_top_level_multibranch_sb`).  Falling back to atom_ref's
    tau@ hint would mis-route us to an enclosing Loop and break
    the translator dispatch.
    """
    if sc.loop_id is not None:
        return sc.loop_id
    if sc.kind == "coverage":
        return None
    for ref in sc.atom_refs:
        if ref.hole_id.startswith("tau@"):
            return ref.hole_id[len("tau@"):]
    return None
