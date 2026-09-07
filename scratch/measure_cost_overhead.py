"""measure_cost_overhead.py — measure the timing overhead of
adding cost_target + cost@L holes to existing benchmark shapes.

For each (baseline, cost-variant) pair, runs each in a fresh
subprocess (matches the regression suite's reproducibility model)
and reports elapsed time.  Computes overhead = (cost_variant
elapsed) / (baseline elapsed).

Both files should produce SAT (same template, same atoms in
common); the cost-variant adds cost candidates + cost_target.
"""
import subprocess
import sys
import time
from pathlib import Path


PAIRS = [
    # (baseline benchmark, cost-variant benchmark)
    ("benchmarks/sumi.py",         "benchmarks/cost_invs/sumi_cost.py"),
    ("benchmarks/mul.py",          "benchmarks/cost_invs/mul_cost.py"),
    ("benchmarks/max_array.py",    "benchmarks/cost_invs/max_array_cost.py"),
    ("benchmarks/array_zero.py",   "benchmarks/cost_invs/array_zero_cost.py"),
    ("benchmarks/nested_loop.py",  "benchmarks/cost_invs/nested_cost.py"),
    ("benchmarks/bubble_sort.py",  "benchmarks/cost_invs/bubble_sort_cost.py"),
]


REPO = Path("/Users/saurabh/code/synthesizer").resolve()
PY = REPO / ".venv" / "bin" / "python"


def time_run(path: str, timeout: int = 600) -> tuple[bool, float, str]:
    """Run `path` in a subprocess, return (success, elapsed, last_line)."""
    full = REPO / path
    t0 = time.monotonic()
    try:
        result = subprocess.run(
            [str(PY), "-u", str(full)],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(REPO),
        )
        elapsed = time.monotonic() - t0
        ok = result.returncode == 0
        last_lines = result.stdout.strip().splitlines()
        last = last_lines[-1] if last_lines else "(no output)"
        return ok, elapsed, last
    except subprocess.TimeoutExpired:
        return False, timeout, "TIMEOUT"


def main():
    print(f"{'pair':<45} {'baseline':>10} {'with cost':>10} {'overhead':>10}")
    print("-" * 80)
    rows = []
    for baseline, cost_variant in PAIRS:
        bl_ok, bl_elapsed, _ = time_run(baseline)
        cv_ok, cv_elapsed, _ = time_run(cost_variant)
        bl_str = f"{bl_elapsed:.2f}s" if bl_ok else "FAIL"
        cv_str = f"{cv_elapsed:.2f}s" if cv_ok else "FAIL"
        overhead = (cv_elapsed / bl_elapsed) if (bl_ok and cv_ok and bl_elapsed > 0) else None
        ov_str = f"{overhead:.2f}x" if overhead else "—"
        pair_label = Path(baseline).name
        print(f"{pair_label:<45} {bl_str:>10} {cv_str:>10} {ov_str:>10}")
        sys.stdout.flush()
        rows.append((pair_label, bl_ok, bl_elapsed, cv_ok, cv_elapsed, overhead))

    print()
    print("Summary:")
    all_passed = all(b_ok and c_ok for _, b_ok, _, c_ok, _, _ in rows)
    print(f"  All pairs SAT: {all_passed}")
    if all_passed:
        ratios = [r[5] for r in rows if r[5] is not None]
        print(f"  Overhead range: {min(ratios):.2f}x to {max(ratios):.2f}x")
        print(f"  Geometric mean: "
              f"{pow(__import__('math').prod(ratios), 1/len(ratios)):.2f}x")


if __name__ == "__main__":
    main()
