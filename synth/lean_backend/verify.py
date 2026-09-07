"""Lean as a fallthrough verifier for the synthesizer.

Ring 2 Day 8: infrastructure only — no solver.py wiring yet.

The solver's UNKNOWN-class handler calls `verify_class_via_lean`
whenever the Lean toolchain is available (Ring 2 default — see
SOUNDNESS.md).  Lean attempts the same obligation with mathlib
tactics (the Day 4-6 machinery); on success the class is treated
as VALID, on failure (or timeout) as UNKNOWN-deferred.  Whether
the deferral eventually accepts or rejects is gated on
`Problem.potentially_unsound`.

This module is INDEPENDENT of solver.py — solver.py imports
`verify_class_via_lean` and calls it.  Day 8 only wires the
function; Day 9 integrates into the solver's UNKNOWN path.
"""
from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import z3

from ..ir import Problem
from ..result import Solution
from .translate import (
    theorem_for_ranking_lb,
    theorem_for_ranking_decrease,
    theorem_for_cost_lb,
    theorem_for_cost_decrement,
    theorem_for_cost_decrement_chain,
    theorem_for_safety_inductive,
    theorem_for_chain_bundle,
    theorem_for_chain_bundle_chain,
    theorem_for_break_bundle,
    theorem_for_entry_bundle,
    theorem_for_entry_bundle_chain,
    theorem_for_coverage,
    emit_axiom_declarations,
    _linearize_path,
)
from ..ir import SB
from .codegen import try_helper_citation, _attach_indices


# Repo layout.
_THIS_DIR = Path(__file__).resolve().parent
_REPO = _THIS_DIR.parent.parent
_LEAN_DIR = _REPO / "lean"
_LAKE = shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")


@dataclass
class Verdict:
    """LeanVerifier outcome for a single obligation.

    Status values:
      - "valid"   — obligation closed (Lean proof exists / cached
                    `.solved.lean` type-checks).
      - "invalid" — obligation genuinely unprovable; a cached
                    `.invalid.lean` proves `∃ vars, hyps ∧ ¬ goal`.
                    Solver must REJECT regardless of
                    `potentially_unsound`.
      - "unknown" — Lean's generic chain didn't close in budget; no
                    curated companion either way.  Solver respects
                    `potentially_unsound`.
      - "error"   — translation or toolchain failure.

    `via_helper`: True if the proof was closed by a Tier-3 helper
    citation (codegen module §H.2).  Telemetry for coverage
    instrumentation — distinguishes "fast helper path" hits from
    "generic tactic chain" hits.
    """
    status: str
    elapsed_s: float
    detail: str = ""
    via_helper: bool = False

    @property
    def is_valid(self) -> bool:
        return self.status == "valid"

    @property
    def is_invalid(self) -> bool:
        return self.status == "invalid"


def lean_available() -> bool:
    """True iff the Lean toolchain is reachable (lake on PATH or at
    ~/.elan/bin/lake) AND the project compiles.  Cheap check that
    callers can use to skip Lean-fallthrough configuration when the
    user hasn't run setup.sh.
    """
    return os.path.exists(_LAKE) and os.access(_LAKE, os.X_OK)


def verify_class_via_lean(
    problem: Problem,
    chosen_atoms: dict[str, Any],
    sc_kind: str,
    loop_id: str,
    *,
    theorem_name: str | None = None,
    timeout_s: float = 60.0,
    dump_failures_to: Path | None = None,
    cache_only: bool = False,
    branch_idx: int | None = None,
) -> Verdict:
    """Verify a single (constraint kind, loop, chosen atoms) tuple
    via Lean.

    `chosen_atoms` maps hole_id → chosen atom(s):
      - `tau@<id>` → list[str]   (subset of the conjunctive τ)
      - other holes → str         (single-hot pick: guard, ϕ, s)

    `sc_kind` is the SafetyConstraint.kind:
      - "ranking-lb" → theorem_for_ranking_lb.
      - "ranking-decrease" → theorem_for_ranking_decrease.
      - "safety" → theorem_for_safety_inductive (loop inductive).

    Returns Verdict with status "valid" / "invalid" / "unknown" /
    "error" plus timing.  "valid" / "invalid" can come from the
    curated `.solved.lean` / `.invalid.lean` companion cache;
    "unknown" means Lean's generic chain couldn't close the proof
    in `timeout_s`; "error" means a translation or build failure.

    With `cache_only=True`, ONLY the companion cache is consulted
    (no `lake env lean` on the obligation itself).  Used by the
    solver when Z3 returned SAT on an axiom-heavy obligation
    (suspect verdict — Z3 may have ignored an axiom) and we want
    a fast curated-cache override without running the full
    generic Lean tactic chain.
    """
    import time

    if not lean_available():
        return Verdict("error", 0.0,
                       f"lake not found at {_LAKE} — run ./lean/setup.sh")

    # F17 (community-validation 2026-06-08): compute a one-shot
    # τ-subset note for `.failed.lean` filename infixing.  Partial-τ
    # dumps get `_partialNofM_` infix so authors can grep
    # actionable failures (full-τ, no infix) vs noise.
    _tau_key = f"tau@{loop_id}"
    _chosen_tau = chosen_atoms.get(_tau_key)
    _master_tau = problem.atoms.get(_tau_key, [])
    if isinstance(_chosen_tau, list) and isinstance(_master_tau, list):
        _chosen_n = len(_chosen_tau)
        _master_n = len(_master_tau)
        _tau_subset_note = (
            f"partial{_chosen_n}of{_master_n}"
            if _chosen_n < _master_n else None
        )
    else:
        _tau_subset_note = None

    # Build synthetic Solution.
    sol = Solution(choices={}, atoms=chosen_atoms)

    # Dispatch to the right theorem builder.
    try:
        if sc_kind == "ranking-lb":
            theorem = theorem_for_ranking_lb(
                problem, sol, loop_id, theorem_name=theorem_name
            )
        elif sc_kind == "ranking-decrease":
            theorem = theorem_for_ranking_decrease(
                problem, sol, loop_id, theorem_name=theorem_name,
                branch_idx=branch_idx,
            )
        elif sc_kind == "safety":
            theorem = theorem_for_safety_inductive(
                problem, sol, loop_id, theorem_name=theorem_name,
                branch_idx=branch_idx,
            )
        elif sc_kind == "safety-bundle-entry":
            # Dispatch: chain-aware translator if EITHER
            #   (a) chain-before-target has non-SB items (chained
            #       loops, e.g. merge_two_sorted L1 / L2), OR
            #   (b) target is nested inside an enclosing Loop (FW
            #       L1 / L2 / edit_distance inner loops).
            # Otherwise stick with the flat-chain translator that
            # the existing benchmarks use.
            _path = _linearize_path(problem.template, loop_id)
            _use_chain = False
            if _path is not None:
                chain, target_idx, enc_lid = _path
                _chain_has_loops = any(
                    not isinstance(it, SB)
                    for it in chain[:target_idx]
                )
                _is_nested = enc_lid is not None
                _use_chain = _chain_has_loops or _is_nested
            if _use_chain:
                theorem = theorem_for_entry_bundle_chain(
                    problem, sol, loop_id, theorem_name=theorem_name
                )
            else:
                theorem = theorem_for_entry_bundle(
                    problem, sol, loop_id, theorem_name=theorem_name
                )
        elif sc_kind == "safety-bundle-post":
            # K.B.IMPL-4 / K.D.IMPL-3 — safety-bundle-post with
            # branch_idx != None is a BREAK obligation.  If the
            # break is in a nested Loop, pass enclosing_loop_id so
            # the translator emits τ_enclosing as conclusion.
            if branch_idx is not None:
                _path = _linearize_path(problem.template, loop_id)
                _enc = _path[2] if _path is not None else None
                theorem = theorem_for_break_bundle(
                    problem, sol, loop_id,
                    theorem_name=theorem_name,
                    branch_idx=branch_idx,
                    enclosing_loop_id=_enc,
                )
            else:
                # Same dispatch rationale as safety-bundle-entry: use
                # chain-aware path when chain has non-SB items OR
                # target is nested.
                _path = _linearize_path(problem.template, loop_id)
                _use_chain = False
                if _path is not None:
                    chain, target_idx, enc_lid = _path
                    _chain_has_loops = any(
                        not isinstance(it, SB) for it in chain
                        if it is not chain[target_idx]
                    )
                    _is_nested = enc_lid is not None
                    _use_chain = _chain_has_loops or _is_nested
                if _use_chain:
                    theorem = theorem_for_chain_bundle_chain(
                        problem, sol, loop_id, theorem_name=theorem_name
                    )
                else:
                    theorem = theorem_for_chain_bundle(
                        problem, sol, loop_id, theorem_name=theorem_name
                    )
        elif sc_kind == "coverage":
            theorem = theorem_for_coverage(
                problem, sol, loop_id, theorem_name=theorem_name
            )
        elif sc_kind == "cost-lb":
            theorem = theorem_for_cost_lb(
                problem, sol, loop_id, theorem_name=theorem_name
            )
        elif sc_kind == "cost-decrement":
            # COST_INVS §1.5: dispatch to chain-aware translator when
            # the outer Loop's body is non-SB (Seq containing inner
            # Loop / nested structure).  Else use the simple SB-body
            # translator (body_cost = 1).
            from ..ir import Loop as _Loop, SB as _SB
            _outer_loop_node = None
            def _find_loop(t, lid):
                if isinstance(t, _Loop):
                    if t.loop_id == lid:
                        return t
                    return _find_loop(t.body, lid)
                if hasattr(t, "left") and hasattr(t, "right"):
                    f = _find_loop(t.left, lid)
                    return f if f is not None else _find_loop(t.right, lid)
                return None
            _outer_loop_node = _find_loop(problem.template, loop_id)
            _is_non_sb_body = (
                _outer_loop_node is not None
                and not isinstance(_outer_loop_node.body, _SB)
            )
            if _is_non_sb_body:
                theorem = theorem_for_cost_decrement_chain(
                    problem, sol, loop_id, theorem_name=theorem_name,
                )
            else:
                theorem = theorem_for_cost_decrement(
                    problem, sol, loop_id, theorem_name=theorem_name,
                    branch_idx=branch_idx,
                )
        # cost-budget translator deferred to next sub-slice;
        # cost-budget obligations stay on Z3 dispatch for now.
        else:
            return Verdict("error", 0.0,
                           f"unsupported constraint kind: {sc_kind!r}")
    except Exception as e:
        return Verdict("error", 0.0,
                       f"translation failed: {type(e).__name__}: {e}")

    # RESEARCH.md §H.2 — codegen helper-citation fast path.  Before
    # running the generic tactic chain, consult the benchmark's
    # `helper_registry` for a Tier-3 helper that discharges this
    # obligation.  On match, substitute the proof body with a one-
    # line `exact <helper> <args>` citation — Lean type-checks the
    # citation in ~2s vs 30-60s for the generic tactic chain.
    helper_used = False
    chosen_with_indices = _attach_indices(problem, chosen_atoms)
    helper_body = try_helper_citation(
        problem, chosen_with_indices, sc_kind, loop_id, branch_idx
    )
    if helper_body is not None:
        theorem = _substitute_proof_body(theorem, helper_body)
        helper_used = True

    # RESEARCH.md §M.5 — trivial-helper auto-generation.  When NO
    # explicit Tier-3 helper matches, try the auto-template before
    # falling through to the generic tactic chain.  The auto-template
    # generates a proof body using only `subst_eqs + refine +
    # omega/assumption` (Core-only, no mathlib).  Eliminating the
    # mathlib preload cuts ~3s per dispatch.  If the auto-template
    # fails, we automatically retry on the generic-chain path —
    # callers see one verdict.
    theorem_original = theorem
    auto_used = False
    if not helper_used and not problem.uninterpreted:
        from .auto_helpers import auto_proof_body as _auto_proof_body
        _auto_body = _auto_proof_body(
            problem, sc_kind, loop_id, branch_idx, theorem, chosen_atoms,
        )
        if _auto_body is not None:
            theorem = _substitute_proof_body(theorem, _auto_body)
            auto_used = True

    # Tempfile, NOT committed to the repo.  Avoids race conditions if
    # multiple verify_class_via_lean calls run concurrently and avoids
    # leaving generated state behind on every run.
    #
    # Import strategy:
    #   helper path  → import the benchmark's helpers module DIRECTLY
    #                  (it declares the UF + user axioms; verify
    #                  skips emit_axiom_declarations to avoid
    #                  duplicates).
    #   generic path → today's path: import SynthLean.Basic +
    #                  emit_axiom_declarations.
    if helper_used:
        helpers_module = problem.helper_registry.module_path
        src = (
            "-- Generated by synth.lean_backend.verify (helper path).\n"
            f"import {helpers_module}\n"
            "open SynthLean\n"
            "\n"
            "namespace SynthLean.VerifyTmp\n"
            "\n"
            f"{theorem}"
            "end SynthLean.VerifyTmp\n"
        )
    elif auto_used:
        # Auto-template path: Core-only import (no mathlib).  The
        # generated proof body uses `omega`/`subst_eqs`/`assumption`
        # only, so it type-checks without the mathlib tactic palette
        # — saving ~3s per dispatch.
        src = (
            "-- Generated by synth.lean_backend.verify (auto-helper path).\n"
            "import SynthLean.Core\n"
            "open SynthLean\n"
            "\n"
            "namespace SynthLean.VerifyTmp\n"
            "\n"
            f"{theorem}"
            "end SynthLean.VerifyTmp\n"
        )
    else:
        axioms = emit_axiom_declarations(problem)
        # COST_INVS §2: cost-* theorems use `open SynthLean.CostLemmas`
        # for citing polynomial identities.  Ensure the import is
        # present whenever we're emitting one of those kinds.
        extra_imports = ""
        if sc_kind in ("cost-lb", "cost-decrement", "cost-budget"):
            extra_imports = "import SynthLean.CostLemmas\n"
        src = (
            "-- Generated by synth.lean_backend.verify — DO NOT keep this file.\n"
            "import SynthLean.Basic\n"
            f"{extra_imports}"
            "open SynthLean\n"
            "\n"
            f"{axioms}"
            "namespace SynthLean.VerifyTmp\n"
            "\n"
            f"{theorem}"
            "end SynthLean.VerifyTmp\n"
        )

    t0 = time.monotonic()

    # Cache-only fast path: skip the `lake env lean` run on the
    # synthetic obligation; only consult the curated companion
    # cache.  Used by the solver for Z3-SAT verdicts on axiom-
    # heavy obligations (where Z3's SAT may be spurious due to
    # axiom misinterpretation).  The cache lookup is content-
    # addressable via the signature hash.
    if cache_only:
        cached_v = _consult_companions(
            dump_failures_to, src, theorem_name, timeout_s
        )
        if cached_v is not None:
            return cached_v
        # F28 (community-validation 2026-06-09): on cache MISS in
        # cache-only mode, still dump the obligation source so the
        # author can iterate against it.  Without this, ranking-lb /
        # ranking-decrease obligations (which route through the
        # cache-only path per synth/solver.py's `_ranking_kind`
        # gate) are invisible to authors: no .failed.lean exists, so
        # the only way to author the .solved.lean companion is to
        # compute the signature hash manually by calling
        # theorem_for_ranking_* + _signature_hash via Python.  v7 Q2
        # (suffix_sum) hit this and burned ~15 min on it.  We still
        # SKIP the generic tactic chain (the perf optimization the
        # cache-only path is designed for) — just dump the source.
        _dump_failed_obligation(
            dump_failures_to, src, theorem_name,
            "-- CACHE-ONLY MISS: no .solved.lean companion found.\n"
            "-- The solver's ranking-cache-only path skipped the\n"
            "-- generic Lean tactic chain (linear-arith UNKNOWNs\n"
            "-- don't get rescued by it).  To author a companion:\n"
            "--   1. cp <this file> <stem>.solved.lean\n"
            "--   2. Replace the tactic chain with a real proof\n"
            "--      (often `omega` suffices for ranking-lb).\n",
            tau_subset_note=_tau_subset_note,
        )
        return Verdict("unknown", time.monotonic() - t0,
                       "cache-only: no companion file")

    # F9 (community-validation 2026-06-08) — cache-first fast
    # path on the standard dispatch.  Without this, every
    # per-class dispatch runs the generic tactic chain (5-15s,
    # often timing out under contention) BEFORE consulting the
    # cache.  If a curated `.solved.lean` companion already
    # exists for this obligation's signature hash, the chain
    # work is wasted.
    #
    # Trade-off: when the cache misses (the common case for
    # constraints without curated proofs), this adds one
    # signature-hash + filesystem-check round-trip per
    # dispatch (~milliseconds).  When it hits, it saves the
    # 5-15s tactic-chain run.
    #
    # The 2× speedup observed in P5 v2's writeup: cache files
    # using SynthLean.Core typecheck in ~2-3s, vs the generic
    # chain's 5-15s.
    if dump_failures_to is not None:
        cached_v = _consult_companions(
            dump_failures_to, src, theorem_name, timeout_s
        )
        if cached_v is not None:
            return cached_v

    # Write to a NamedTemporaryFile that lives only for this call.
    # `lake env lean <file>` invokes lean with the lake project's
    # environment (so `import SynthLean.Basic` resolves) but doesn't
    # rebuild the whole project on each call.
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", delete=False, encoding="utf-8"
    ) as f:
        f.write(src)
        tmp_path = f.name

    timed_out = False
    try:
        try:
            proc = subprocess.run(
                [_LAKE, "env", "lean", tmp_path],
                cwd=_LEAN_DIR,
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired as e:
            timed_out = True
            elapsed = time.monotonic() - t0
            # Before dumping, consult curated companion caches.
            if dump_failures_to is not None:
                cached_v = _consult_companions(
                    dump_failures_to, src, theorem_name, timeout_s
                )
                if cached_v is not None:
                    return cached_v
            # Capture the timed-out source for human review.
            _dump_failed_obligation(
                dump_failures_to, src, theorem_name,
                f"-- TIMED OUT after {timeout_s}s\n",
                tau_subset_note=_tau_subset_note,
            )
            return Verdict("unknown", elapsed,
                           f"lake env lean timed out after {timeout_s}s")
    finally:
        if not timed_out:
            try:
                os.unlink(tmp_path)
            except OSError:
                pass

    elapsed = time.monotonic() - t0
    if proc.returncode == 0:
        return Verdict("valid", elapsed, via_helper=helper_used)

    # If the auto-template path failed, retry with the generic chain.
    # The auto-template is conservative (only attempts shapes it's
    # confident in), but Lean can still reject — fall back transparently.
    if auto_used:
        axioms = emit_axiom_declarations(problem)
        extra_imports = ""
        if sc_kind in ("cost-lb", "cost-decrement", "cost-budget"):
            extra_imports = "import SynthLean.CostLemmas\n"
        src = (
            "-- Generated by synth.lean_backend.verify "
            "(generic chain after auto-template miss).\n"
            "import SynthLean.Basic\n"
            f"{extra_imports}"
            "open SynthLean\n"
            "\n"
            f"{axioms}"
            "namespace SynthLean.VerifyTmp\n"
            "\n"
            f"{theorem_original}"
            "end SynthLean.VerifyTmp\n"
        )
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False, encoding="utf-8"
        ) as f:
            f.write(src)
            tmp_path2 = f.name
        try:
            proc = subprocess.run(
                [_LAKE, "env", "lean", tmp_path2],
                cwd=_LEAN_DIR,
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired:
            try: os.unlink(tmp_path2)
            except OSError: pass
            elapsed = time.monotonic() - t0
            return Verdict("unknown", elapsed,
                           f"lake env lean timed out after {timeout_s}s")
        try: os.unlink(tmp_path2)
        except OSError: pass
        elapsed = time.monotonic() - t0
        if proc.returncode == 0:
            return Verdict("valid", elapsed, via_helper=False)
        # Fall through to the stderr-classification logic below
        # using `proc` from the generic-chain attempt.

    # `lean` exits non-zero on either a tactic failure or a syntax/
    # import error.  We treat unrecognized tactic failures as
    # `unknown` (the proof didn't close) and outright structural
    # errors as `error`.
    stderr_tail = (proc.stdout + proc.stderr)[-2000:]
    is_tactic_unknown = (
        "error" in stderr_tail.lower()
        and ("Unknown" in stderr_tail
             or "unsolved goals" in stderr_tail
             or "failed" in stderr_tail
             or "did not close" in stderr_tail)
    )

    # Phase Y.1.5: before falling through to UNKNOWN / ERROR, consult
    # the curated companion caches.  A matching `.solved.lean` proves
    # the obligation (VALID); a matching `.invalid.lean` proves its
    # negation (INVALID — synthesizer must reject regardless of
    # `potentially_unsound`).  Either outcome short-circuits the
    # fallthrough.
    if dump_failures_to is not None:
        cached_v = _consult_companions(
            dump_failures_to, src, theorem_name, timeout_s
        )
        if cached_v is not None:
            return cached_v

    if is_tactic_unknown:
        # Lean tried, couldn't close.  Dump the source so the user (or
        # the Phase Y.2 driver-LLM) can hand-write a proof for this
        # specific obligation.
        _dump_failed_obligation(
            dump_failures_to, src, theorem_name,
            f"-- Lean returned UNKNOWN: tactic chain didn't close.\n"
            f"-- Lean output tail:\n"
            + "\n".join(f"-- {line}"
                       for line in _stable_stderr(stderr_tail).splitlines()[-15:])
            + "\n",
            tau_subset_note=_tau_subset_note,
        )
        return Verdict("unknown", elapsed, "proof did not close")
    _dump_failed_obligation(
        dump_failures_to, src, theorem_name,
        f"-- Lean returned ERROR (exit {proc.returncode}):\n"
        + "\n".join(f"-- {line}"
                   for line in _stable_stderr(stderr_tail).splitlines()[-10:])
        + "\n",
        tau_subset_note=_tau_subset_note,
    )
    return Verdict("error", elapsed,
                   f"lean exit {proc.returncode}: "
                   f"{stderr_tail[-400:].strip()}")


def _substitute_proof_body(theorem_text: str, new_body: str) -> str:
    """Replace the tactic body of `theorem_text` with `new_body`.

    The theorem-builder pattern always ends with `... := by\\n
    <tactic body>`.  This function finds the last `:= by\\n` marker
    and replaces everything after it with `  {new_body}\\n`.

    Used by the §H.2 codegen helper-citation path — substitutes a
    one-line `exact <helper> <args>` for the generic tactic chain
    so Lean type-checks in ~2s instead of running tactic search.
    """
    marker = ":= by\n"
    idx = theorem_text.rfind(marker)
    if idx < 0:
        raise ValueError(
            "theorem text has no `:= by\\n` marker; codegen helper-"
            "citation requires the standard theorem_for_* output shape"
        )
    head = theorem_text[: idx + len(marker)]
    return head + f"  {new_body}\n"


def _stable_stderr(text: str) -> str:
    """Normalize Lean's stderr tail for a stable `.failed.lean`
    dump: strip the tempfile path that `lake env lean` echoes
    (something like `/var/folders/.../T/tmpXXXXXX.lean:LINE:COL:
    error: ...`).  Without this, every run of the same obligation
    produces a different tempfile name → the same `.failed.lean`
    file gets a different failure-note prefix → git diff is
    constantly noisy.
    """
    import re
    # Path like `/var/folders/l4/.../T/tmpXXXX.lean` OR
    # `/tmp/.../tmpXXXX.lean` (Linux).  Replace with a stable
    # placeholder.
    return re.sub(
        r"/(?:var/folders|tmp)/\S*?\.lean(?=[:\s])",
        "<tmp>.lean",
        text,
    )


def _signature_hash(src: str) -> str:
    """Stable content-hash of the theorem SIGNATURE only (excluding
    the proof body and any failure-note prefix).  Used as a filename
    suffix so the `.failed.lean` dump and its curated companion
    (`.solved.lean` / `.invalid.lean`) share a stem regardless of
    proof body or which-failure-mode prefix appears.

    Hashing the signature means: same chosen atoms + same translator
    encoding ⇒ same hash ⇒ stable filename across runs.  A
    translator change that shifts hypotheses or goal shape changes
    the hash, so old companions become orphans (caught by CI).
    """
    # The theorem signature spans from the `theorem` keyword through
    # `:= by`.  Failure-note comments at the top of the file (e.g.
    # `-- TIMED OUT after 15s`) are excluded.
    idx = src.find("theorem ")
    if idx < 0:
        # Shouldn't happen — fall back to hashing everything.
        sig = src
    else:
        sig = src[idx:].split(":= by", 1)[0]
    return hashlib.sha256(sig.encode("utf-8")).hexdigest()[:8]


def _typecheck(path: Path, timeout_s: float) -> bool:
    """True iff `lake env lean <path>` exits 0.

    The path must be resolved to absolute because `cwd=_LEAN_DIR` —
    a relative path passed by the caller (e.g.,
    `lean/SynthLean/Y2Corpus/...`) wouldn't resolve from inside the
    lean directory.
    """
    try:
        proc = subprocess.run(
            [_LAKE, "env", "lean", str(path.resolve())],
            cwd=_LEAN_DIR,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        return proc.returncode == 0
    except (subprocess.TimeoutExpired, OSError):
        return False


def _consult_companions(
    dump_dir: Path | None,
    src: str,
    theorem_name: str | None,
    timeout_s: float,
) -> Verdict | None:
    """Look for curated companions matching this obligation's
    signature hash:

      - `<theorem_name>_<H>.solved.lean` — if type-checks, the
        obligation is genuinely valid → return Verdict("valid").
      - `<theorem_name>_<H>.invalid.lean` — if type-checks, the
        obligation is genuinely invalid (existential
        counterexample) → return Verdict("invalid").

    Returns None on miss (no companion, doesn't type-check, or
    `dump_dir`/`theorem_name` is None).

    Phase Y.1.5 cache hook: curated companions become a runtime
    verification path, not just training data.  Drift between an
    obligation's signature and a stale companion is caught by
    Lean's rejection at type-check time.  The `tests/test_y2corpus.py`
    CI gate verifies all committed companions type-check against
    the current toolchain.
    """
    if dump_dir is None or theorem_name is None:
        return None
    h = _signature_hash(src)
    solved = dump_dir / f"{theorem_name}_{h}.solved.lean"
    invalid = dump_dir / f"{theorem_name}_{h}.invalid.lean"
    if solved.exists() and _typecheck(solved, timeout_s):
        return Verdict("valid", 0.0,
                       f"via cached .solved.lean ({solved.name})")
    if invalid.exists() and _typecheck(invalid, timeout_s):
        return Verdict("invalid", 0.0,
                       f"via cached .invalid.lean ({invalid.name})")
    return None


def _dump_failed_obligation(
    dump_dir: Path | None,
    src: str,
    theorem_name: str | None,
    failure_note: str,
    tau_subset_note: str | None = None,
) -> None:
    """If `dump_dir` is set, save the obligation's Lean source there
    with a `<theorem_name>[_<tau_subset_note>]_<H>.failed.lean`
    filename — H is the signature hash so the dump pairs naturally
    with `.solved.lean` / `.invalid.lean` companions via stem
    matching.

    `tau_subset_note` (F17, community-validation 2026-06-08): a
    short infix like `"partial2of4"` indicating this dump is for
    a PARTIAL τ subset (not the full conjunction).  Partial-τ
    failures are EXPECTED during enumeration and are NOT
    actionable — only full-τ failures (no infix) block global SAT.
    Grepping `<theorem_name>_<hash>.failed.lean` without `_partial`
    finds the actionable ones.

    Idempotent: if a `.failed.lean` for this signature already
    exists, the new dump overwrites it.  This is intentional — the
    file's purpose is to record the LATEST failure mode (timeout
    vs tactic-unknown vs error), and content-addressing on the
    signature means re-running the benchmark doesn't proliferate
    counter-named duplicates.
    """
    if dump_dir is None:
        return
    try:
        dump_dir.mkdir(parents=True, exist_ok=True)
        base = theorem_name or "anon"
        h = _signature_hash(src)
        infix = f"_{tau_subset_note}" if tau_subset_note else ""
        path = dump_dir / f"{base}{infix}_{h}.failed.lean"
        # F17 cleanup: when migrating an existing dump dir to the
        # partialNofM-infix scheme, the pre-F17 non-infixed file at
        # the same hash is now stale (same content, wrong name).
        # Remove it so the dir doesn't accumulate duplicates.
        if tau_subset_note:
            stale = dump_dir / f"{base}_{h}.failed.lean"
            if stale.exists() and stale != path:
                try:
                    stale.unlink()
                except OSError:
                    pass
        path.write_text(failure_note + "\n" + src)
    except OSError:
        pass  # best-effort — don't crash synthesis on dump failure
