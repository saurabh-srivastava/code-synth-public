"""Single-benchmark subprocess runner for `tests/regression.py`.

Loads a benchmark `.py` file, runs `solve()` on its `PROBLEM`, prints
one JSON line on stdout with the result.  `regression.py` invokes
this script per-benchmark via `subprocess.run` so each gets a fresh
Python interpreter — eliminates order-dependent Z3 state leakage
that has historically produced:

  - Flaky solution counts (matrix_init: 6s standalone, 369s after a
    heavy preceding run).
  - Z3 nondeterminism picking lower-score-but-soundness-buggy
    winners (rec_const flake, Phase 5.B).

This is a reproducibility guard, not a performance optimization.
Subprocess startup is ~1–2s per benchmark — acceptable.

Usage:

    python tests/_solve_one.py benchmarks/intsqrt.py
"""
from __future__ import annotations
import importlib.util
import json
import sys
import time
from pathlib import Path


def main(rel_path: str) -> int:
    REPO = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(REPO))
    from synth import solve, SolveResult, NoSolution, Timeout

    full_path = REPO / rel_path
    spec = importlib.util.spec_from_file_location("_bench", full_path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    try:
        spec.loader.exec_module(mod)
    except Exception as e:
        print(json.dumps({
            "path": rel_path,
            "error": f"load: {type(e).__name__}: {e}",
        }))
        return 1

    if not hasattr(mod, "PROBLEM"):
        print(json.dumps({"path": rel_path, "skip": "no PROBLEM global"}))
        return 0

    expected = getattr(mod.PROBLEM, "expected_solutions", None)
    # Discrimination tests: module declares `EXPECT_NO_SOLUTION = True`
    # when ALL candidates are deliberately invalid (e.g. wrong-coefficient
    # Toom-3, 2-mult Karatsuba) and we want the runner to PASS only when
    # synthesis correctly returns NoSolution.  Soundness guard.
    expect_no_solution = bool(getattr(mod, "EXPECT_NO_SOLUTION", False))
    start = time.monotonic()
    try:
        result = solve(mod.PROBLEM)
    except Exception as e:
        print(json.dumps({
            "path": rel_path,
            "elapsed": time.monotonic() - start,
            "expected": expected,
            "error": f"solve: {type(e).__name__}: {e}",
        }))
        return 1
    elapsed = time.monotonic() - start

    expected_lean = getattr(mod.PROBLEM, "expected_lean_hits", None)
    payload: dict = {
        "path": rel_path,
        "elapsed": round(elapsed, 2),
        "expected": expected,
        "expected_lean_hits": expected_lean,
        "expect_no_solution": expect_no_solution,
    }
    if isinstance(result, SolveResult):
        payload["result_type"] = "SolveResult"
        payload["solutions"] = len(result.solutions)
    elif isinstance(result, NoSolution):
        payload["result_type"] = "NoSolution"
        payload["reason"] = result.reason
        payload["hints"] = list(getattr(result, "hints", []))
    elif isinstance(result, Timeout):
        payload["result_type"] = "Timeout"
        payload["budget"] = result.budget_seconds
    else:
        payload["result_type"] = type(result).__name__
    # Lean-dispatch stats are populated on every result type.
    ld = getattr(result, "lean_dispatch", None)
    if ld is not None:
        payload["lean_dispatch"] = ld.to_dict()

    print(json.dumps(payload))
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: _solve_one.py <benchmark.py>", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
