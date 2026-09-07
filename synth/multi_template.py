"""Parallel multi-template synthesis harness.

Runs N `Problem` variants in parallel subprocesses and aggregates
the results.  Each variant is a complete, self-contained `Problem`;
the harness orchestrates parallelism + result collection.

Why subprocess parallelism instead of unified-SAT:
  - Templates don't share indicator bits (different loop_ids,
    different hole IDs), so a single SAT can't usefully amortize
    cross-template search.
  - Z3 runs single-threaded for SAT — process-level parallelism
    is the cleanest speedup dimension.
  - 'spawn' isolation (via concurrent.futures.ProcessPoolExecutor)
    matches `tests/regression.py`'s pattern — Z3 state can't leak
    between variants.
  - Per-template Tier-3 helpers and dump directories stay
    naturally separated.

Architecture decision recorded in RESEARCH.md §I.
"""
from __future__ import annotations
import multiprocessing
import time
import traceback
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from typing import Any

from .ir import Problem


@dataclass
class VariantResult:
    """Per-variant outcome."""
    name: str
    status: str        # "success" | "no_solution" | "timeout" | "error"
    elapsed_s: float
    result: Any        # SolveResult | NoSolution | Timeout | error string

    @property
    def score(self) -> float | None:
        """Best solution's score, or None if no success."""
        if self.status != "success":
            return None
        sols = getattr(self.result, "solutions", None)
        if not sols:
            return None
        return min(s.score for s in sols)


@dataclass
class MultiTemplateResult:
    """Aggregate of N variant results, preserving input ordering."""
    variants: list[VariantResult]

    def __bool__(self) -> bool:
        return any(v.status == "success" for v in self.variants)

    @property
    def successful(self) -> list[VariantResult]:
        return [v for v in self.variants if v.status == "success"]

    @property
    def best(self) -> VariantResult | None:
        wins = [v for v in self.successful if v.score is not None]
        if not wins:
            return None
        return min(wins, key=lambda v: v.score)  # type: ignore[arg-type]


def _solve_worker(args: tuple[str, Problem]) -> tuple[str, str, float, Any]:
    """Subprocess worker: solve one variant, return outcome tuple.

    Returns (name, status, elapsed_s, result_or_error).  Module-
    level so ProcessPoolExecutor can pickle + spawn.
    """
    name, problem = args
    t = time.monotonic()
    try:
        # Import inside the worker so Z3 init happens per-subprocess
        # — matches the regression's `_solve_one.py` isolation pattern.
        from . import solve
        from .result import SolveResult, NoSolution, Timeout
        r = solve(problem)
    except Exception:
        return (name, "error", time.monotonic() - t,
                traceback.format_exc())
    elapsed = time.monotonic() - t
    if isinstance(r, SolveResult):
        return (name, "success", elapsed, r)
    if isinstance(r, NoSolution):
        return (name, "no_solution", elapsed, r)
    if isinstance(r, Timeout):
        return (name, "timeout", elapsed, r)
    return (name, "unknown", elapsed, r)


def multi_template_solve(
    variants: list[tuple[str, Problem]],
    *,
    parallel: bool = True,
    max_workers: int | None = None,
) -> MultiTemplateResult:
    """Run N variants and return aggregated results, preserving order.

    Args:
        variants: list of (name, Problem) pairs.  Each Problem is
            a complete, independent synthesis problem.
        parallel: if True, dispatch via ProcessPoolExecutor;
            otherwise sequential (useful for debugging).
        max_workers: cap on parallel workers.  Defaults to
            min(len(variants), cpu_count).

    Returns:
        MultiTemplateResult with per-variant outcomes in input order.
    """
    if not variants:
        return MultiTemplateResult(variants=[])

    if not parallel:
        outs = [_solve_worker(v) for v in variants]
    else:
        workers = max_workers or min(len(variants),
                                     multiprocessing.cpu_count())
        with ProcessPoolExecutor(max_workers=workers) as ex:
            futures = {ex.submit(_solve_worker, v): i
                       for i, v in enumerate(variants)}
            outs_indexed: list[tuple[int, tuple[str, str, float, Any]]] = []
            for fut in as_completed(futures):
                idx = futures[fut]
                outs_indexed.append((idx, fut.result()))
        # Re-order to match input.
        outs_indexed.sort(key=lambda x: x[0])
        outs = [t for _, t in outs_indexed]

    results = [VariantResult(name=o[0], status=o[1],
                             elapsed_s=o[2], result=o[3])
               for o in outs]
    return MultiTemplateResult(variants=results)
