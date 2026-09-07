"""CLI entry point — load a Problem from JSON or Python, run solve, print.

Usage:

    python -m synth <problem.json>
    python -m synth <module.py>            # imports and uses PROBLEM
    python -m synth - < problem.json       # stdin

The Python form imports the module and uses its `PROBLEM` global, so
existing eDSL benchmarks (`benchmarks/intsqrt.py` etc.) work as-is.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import sys
from pathlib import Path

from .parse import load_problem_json, problem_from_dict
from .solver import solve
from .result import SolveResult, NoSolution, Timeout


def _load(source: str):
    if source == "-":
        return problem_from_dict(json.loads(sys.stdin.read()))
    p = Path(source)
    if not p.exists():
        raise FileNotFoundError(source)
    if p.suffix == ".json":
        return load_problem_json(p)
    if p.suffix == ".py":
        spec = importlib.util.spec_from_file_location("_problem", p)
        mod = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(mod)
        if not hasattr(mod, "PROBLEM"):
            raise AttributeError(f"{p}: module defines no PROBLEM global")
        return mod.PROBLEM
    raise ValueError(f"unsupported extension: {p.suffix!r}")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source", help="problem file (.json or .py) or '-' for stdin")
    ap.add_argument("--max-solutions", type=int, default=None,
                    help="override Problem.max_solutions")
    ap.add_argument("--timeout-ms", type=int, default=None,
                    help="override Problem.solver_timeout_ms")
    ap.add_argument(
        "--potentially-unsound", action="store_true",
        help=(
            "Allow synthesis to succeed by accepting obligations "
            "neither Z3 nor Lean could verify (lenient fallback).  "
            "By default the synthesizer only emits provably-correct "
            "code — see SOUNDNESS.md.  Use this flag when you've "
            "verified the obligations externally and need synthesis "
            "to complete despite undecided checks."
        ),
    )
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args(argv)

    problem = _load(args.source)
    if args.max_solutions is not None:
        problem.max_solutions = args.max_solutions
    if args.timeout_ms is not None:
        problem.solver_timeout_ms = args.timeout_ms
    if args.potentially_unsound:
        problem.potentially_unsound = True

    result = solve(problem)

    if isinstance(result, SolveResult):
        print(f"SAT — {len(result.solutions)} solution(s)\n")
        for n, sol in enumerate(result.solutions):
            print(f"── solution #{n}  score={sol.score:g} ──")
            print(sol.code)
            if args.verbose:
                print("\n  choices:")
                for hid in sorted(sol.choices):
                    print(f"    {hid:10s} → [#{sol.choices[hid]}]  "
                          f"{sol.atoms[hid]!r}")
            print()
        return 0

    if isinstance(result, NoSolution):
        print(f"UNSAT — {result.reason}")
        if result.unsat_core:
            print(f"  unsat core: {result.unsat_core}")
        for h in result.hints:
            print(f"  hint: {h}")
        return 2

    if isinstance(result, Timeout):
        print(f"TIMEOUT — {result.reason} (budget={result.budget_seconds}s)")
        print(f"  hole sizes: {result.hole_sizes}")
        if result.partial_solutions:
            print(f"  found {len(result.partial_solutions)} partial solution(s) "
                  "before timeout")
        for h in result.hints:
            print(f"  hint: {h}")
        return 3

    raise AssertionError(f"unknown result type: {type(result).__name__}")


if __name__ == "__main__":
    raise SystemExit(main())
