"""Regression suite — runs benchmarks, reports SAT/UNSAT/TIMEOUT + timing.

Default (quick) suite skips axiom-heavy benchmarks that take minutes.
Pass `--slow` to include them.

    .venv/bin/python tests/regression.py            # quick suite (~20s)
    .venv/bin/python tests/regression.py --slow     # adds fib (~5 min)

Exit code: number of failing benchmarks.

**Subprocess isolation.**  Each benchmark runs in its own Python
interpreter (via `tests/_solve_one.py`).  Pre-isolation, in-process
Z3 state leakage produced order-dependent results: matrix_init
went 6s standalone → 369s after grid_paths ran first; rec_const
flaked between sound and unsound winners depending on what
preceded it (Phase 5.B).  Subprocess isolation is the
non-negotiable reproducibility guard for a soundness-oracle test
suite.  Cost: ~1–2s per benchmark for Python startup; total quick
suite ~30s longer than the unsafe in-process version.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import subprocess
import sys
import time
from pathlib import Path

# Quick suite: everything that finishes in seconds under the current
# PLDI'09-reduction solver.  Excludes axiom-heavy benchmarks (Fibonacci)
# whose per-check Z3 quantifier work dominates runtime.
QUICK = [
    "benchmarks/intsqrt.py",
    "benchmarks/sumi.py",
    "benchmarks/mul.py",
    "benchmarks/swap.py",
    "benchmarks/strassen.py",
    "benchmarks/abs.py",
    "benchmarks/sat_sub.py",
    "benchmarks/max_array.py",
    "benchmarks/array_zero.py",
    "benchmarks/rec_const.py",
    "benchmarks/rec_neg.py",
    "benchmarks/rec_zero_array.py",
    "benchmarks/rec_zero_array_chain.py",
    "benchmarks/rec_zero_double.py",
    "benchmarks/rec_zero_array_branched.py",
    "benchmarks/rec_clamped_phi.py",
    "benchmarks/nested_loop.py",
    "benchmarks/nested_zero_array.py",
    "benchmarks/intdiv.py",
    "benchmarks/bresenham.py",
    "benchmarks/bresenham_full.py",
    "benchmarks/bubble_sort.py",
    "benchmarks/insertion_sort.py",
    "benchmarks/matrix_init.py",
    "benchmarks/sum_array.py",
    # Phase X corpus benchmarks.
    "benchmarks/min_array.py",
    "benchmarks/array_fill.py",
    "benchmarks/array_copy.py",
    "benchmarks/increment_array.py",
    "benchmarks/negate_array.py",
    "benchmarks/max2.py",
    "benchmarks/add_arrays.py",
    "benchmarks/clamp_array_positive.py",
    "benchmarks/array_double.py",
    "benchmarks/subtract_arrays.py",
    "benchmarks/min_index.py",
    "benchmarks/array_swap.py",
    "benchmarks/linear_combination.py",
    "benchmarks/pairwise_max.py",
    "benchmarks/max3.py",
    # Phase X batch 4: shape-variety + acyclic + 3-way branching.
    "benchmarks/abs_diff.py",
    "benchmarks/last_element.py",
    "benchmarks/mid3.py",
    "benchmarks/swap_first_last.py",
    "benchmarks/scalar_clamp.py",
    "benchmarks/range_init.py",
    # Phase X batch 5: loop-with-conditional-array-write +
    # multi-output reductions + max-index variant.
    "benchmarks/abs_array.py",
    "benchmarks/saturate_add.py",
    "benchmarks/max_min_diff.py",
    "benchmarks/array_max_index.py",
    # Phase X batch 6: array writes, predicate-folding loop,
    # SB(n=4) N-way scalar.
    "benchmarks/array_increment_at.py",
    "benchmarks/all_positive.py",
    "benchmarks/array_set_const.py",
    "benchmarks/scalar_max4.py",
    # Phase X batch 7: array concat + early-exit + multi-output.
    "benchmarks/array_concat.py",
    "benchmarks/find_first_pos.py",
    "benchmarks/min_max_pair.py",
    "benchmarks/array_rotate_left.py",
    "benchmarks/array_shift_right.py",
    # Phase X batch 8: scalar predicates + array reductions.
    "benchmarks/array_max_val.py",
    "benchmarks/array_min_val.py",
    "benchmarks/abs2.py",
    "benchmarks/sign.py",
    "benchmarks/range_init_offset.py",
    # Phase X batch 9 (final): in-place reverse, parametric search,
    # scalar/array clamping reductions.  Hits the 50-benchmark
    # Phase X target.
    "benchmarks/reverse_array.py",
    "benchmarks/is_sorted.py",
    "benchmarks/scalar_min4.py",
    "benchmarks/clamp_array_range.py",
    "benchmarks/array_index_of.py",
    "benchmarks/cover_loop_branched_recur.py",
    "benchmarks/cover_chain_branched_recur.py",
]

# Slow suite: axiom-heavy or otherwise long-running benchmarks.
# All axiom-heavy benchmarks synthesize SOUND (default
# `potentially_unsound = False`) via the chain-bundle Lean
# translator + curated `.solved.lean` for sc#1 + sc#4 (and per-
# branch sc#N for SB(n>1) bodies — count_zeros, count_equal,
# array_neg_count).  Each takes 3-26 min wall time depending on
# axiom shape and inner-body branching.
SLOW = [
    "benchmarks/fib.py",
    "benchmarks/selection_sort.py",
    "benchmarks/factorial.py",
    "benchmarks/array_product.py",
    "benchmarks/count_zeros.py",
    "benchmarks/count_equal.py",
    "benchmarks/dot_product.py",
    "benchmarks/sum_first_k.py",
    "benchmarks/array_neg_count.py",
    "benchmarks/gcd.py",
    "benchmarks/power_of_two.py",
]

# Phase X.S stretch benchmarks.  See RESEARCH.md §D.1.5.
# Each Problem in benchmarks/stretch/ sets `xfail_reason: str | None`
# on a top-level module attribute; the runner treats xfail benchmarks
# as soft-expected failures (does not count as a pass OR a fail).
STRETCH = [
    # (a) Hardest HE+/MBPP+ representatives
    "benchmarks/stretch/binary_search.py",
    "benchmarks/stretch/merge_two_sorted.py",
    "benchmarks/stretch/majority_element.py",
    "benchmarks/stretch/kadane_max_subarray.py",
    "benchmarks/stretch/edit_distance.py",
    # (b) Edge-of-open-problem algorithms
    "benchmarks/stretch/strassen_3x3_laderman.py",
    "benchmarks/stretch/karatsuba_deg2.py",
    "benchmarks/stretch/toom3_deg2.py",  # Added 2026-05-17.
    "benchmarks/stretch/modular_exponentiation.py",
    "benchmarks/stretch/floyd_warshall.py",
    "benchmarks/stretch/boolean_matmul_3x3.py",
    # Discrimination tests — EXPECT_NO_SOLUTION = True.  These
    # benchmarks declare invalid candidate sets; passing means
    # synth correctly returned NoSolution.  Soundness regression
    # guards against the verifier accepting unsound candidates.
    "benchmarks/stretch/karatsuba_deg2_discrim_2mult.py",
    "benchmarks/stretch/toom3_deg2_discrim_wrong_coef.py",
    # Edge-of-open research benchmark: search for 22-product 3x3
    # matmul algorithm.  All hand-crafted candidates rejected
    # (proved offline via linear-algebra rank check).  Acceptance
    # would be a major discovery OR a soundness bug.
    "benchmarks/stretch/strassen_3x3_lt23mult_search.py",
]

# Per-benchmark subprocess timeout.  Generous because sound-mode
# axiom-heavy benchmarks can take 10+ min on cold caches; the
# per-benchmark `solver_timeout_ms` is the real bound on synthesis
# time.  Nightly CI 2026-05-18: count_zeros wedged at 1800.1s (was
# right at the budget — see Phase X.S commit history); bumped to
# 2700s (45 min) to give cloud-noise headroom while staying well
# under the workflow's 240-min job cap.
SUBPROCESS_TIMEOUT_S = 2700


def _run_one(repo_root: Path, helper: Path, rel: str
             ) -> tuple[dict | None, str, str, int]:
    """Run a single benchmark in a subprocess.

    Returns `(payload, stdout, stderr, returncode)`.  `payload` is the
    parsed JSON from the helper's last stdout line, or None if parsing
    failed.
    """
    try:
        proc = subprocess.run(
            [sys.executable, str(helper), rel],
            capture_output=True, text=True,
            cwd=repo_root,
            timeout=SUBPROCESS_TIMEOUT_S,
        )
    except subprocess.TimeoutExpired as e:
        return (
            {"result_type": "Timeout", "subprocess_timeout": True},
            (e.stdout or b"").decode("utf-8", "replace"),
            (e.stderr or b"").decode("utf-8", "replace"),
            -1,
        )
    payload = None
    if proc.stdout.strip():
        # The helper prints one JSON line.  Parse the last non-empty
        # line so any incidental stderr-redirected noise is tolerated.
        for line in reversed(proc.stdout.strip().splitlines()):
            line = line.strip()
            if not line:
                continue
            try:
                payload = json.loads(line)
                break
            except json.JSONDecodeError:
                continue
    return payload, proc.stdout, proc.stderr, proc.returncode


def run(files: list[str]) -> int:
    repo_root = Path(__file__).resolve().parent.parent
    helper = repo_root / "tests" / "_solve_one.py"
    ok = fail = 0

    # Load baseline timings.  Used for soft timing-regression
    # annotations — flag when current elapsed deviates from
    # baseline by ≥ threshold.  Doesn't fail the test (CI machines
    # vary), but surfaces drift without forcing a fresh main rerun.
    timings_path = repo_root / "tests" / "regression_timings.json"
    timings: dict = {}
    timing_slow_threshold = 1.5
    timing_fast_threshold = 0.5
    timing_min_baseline = 1.0
    if timings_path.exists():
        try:
            data = json.loads(timings_path.read_text())
            timing_slow_threshold = data.get(
                "_threshold_slow", timing_slow_threshold)
            timing_fast_threshold = data.get(
                "_threshold_fast", timing_fast_threshold)
            timing_min_baseline = data.get(
                "_min_baseline_s", timing_min_baseline)
            timings = {k: v for k, v in data.items()
                       if not k.startswith("_")}
        except Exception as e:
            print(f"(timings file unreadable: {e}; skipping checks)")

    slow_drifts: list[tuple[str, float, float]] = []  # (rel, baseline, current)
    fast_drifts: list[tuple[str, float, float]] = []
    missing_baseline: list[str] = []

    def _timing_note(rel: str, elapsed: float) -> str:
        """Compare elapsed vs baseline; return soft annotation."""
        baseline = timings.get(rel)
        if baseline is None:
            missing_baseline.append(rel)
            return ""
        if baseline < timing_min_baseline:
            return ""  # sub-second baselines too noisy to compare
        ratio = elapsed / baseline if baseline > 0 else 0
        if ratio >= timing_slow_threshold:
            slow_drifts.append((rel, baseline, elapsed))
            return f" [SLOW: {ratio:.1f}x baseline {baseline:.1f}s]"
        if ratio <= timing_fast_threshold:
            fast_drifts.append((rel, baseline, elapsed))
            return f" [FAST: {ratio:.1f}x baseline {baseline:.1f}s]"
        return ""

    for rel in files:
        t0 = time.monotonic()
        payload, stdout, stderr, returncode = _run_one(
            repo_root, helper, rel
        )
        wall = time.monotonic() - t0

        if payload is None:
            print(f"{rel:<40} ERROR — subprocess output unparseable "
                  f"(returncode {returncode}, {wall:.1f}s wall)")
            if stderr.strip():
                print(f"    stderr: {stderr.strip()[-400:]}")
            fail += 1
            continue

        if "skip" in payload:
            print(f"{rel:<40} SKIP — {payload['skip']}")
            continue
        if "error" in payload:
            print(f"{rel:<40} ERROR — {payload['error']}  "
                  f"({wall:.1f}s wall)")
            fail += 1
            continue

        elapsed = payload.get("elapsed", wall)
        rt = payload["result_type"]
        ld = payload.get("lean_dispatch", {"valid": 0, "unknown": 0,
                                            "errors": 0})
        lean_note = ""
        if ld["valid"] or ld["unknown"] or ld["errors"]:
            lean_note = (f" [Lean: {ld['valid']}✓ "
                         f"{ld['unknown']}?, {ld['errors']}✗]")
        # Discrimination tests: ALL candidates are deliberately invalid;
        # NoSolution is the expected (passing) outcome, SolveResult is
        # the failing outcome.  Inverts the usual pass/fail logic.
        expect_no_solution = bool(payload.get("expect_no_solution", False))
        if expect_no_solution:
            if rt == "NoSolution":
                print(f"{rel:<40} DISCRIM-PASS — correctly rejected "
                      f"({elapsed:.1f}s)")
                ok += 1
            elif rt == "SolveResult":
                n_sols = payload["solutions"]
                print(f"{rel:<40} DISCRIM-FAIL — synth returned "
                      f"{n_sols} solution(s) for an invalid problem  "
                      f"({elapsed:.1f}s)")
                fail += 1
            else:
                print(f"{rel:<40} DISCRIM-INCONCLUSIVE — {rt}  "
                      f"({elapsed:.1f}s)")
                fail += 1
            continue
        if rt == "SolveResult":
            n_sols = payload["solutions"]
            expected = payload.get("expected")
            expected_lean = payload.get("expected_lean_hits")
            mismatches = []
            if expected is not None and n_sols != expected:
                # Soundness guard: a constraint accidentally dropped
                # from emission widens the solution set without
                # breaking the post.  See CLAUDE.md Lesson #31.
                mismatches.append(
                    f"solution count {n_sols} ≠ expected {expected}"
                )
            # Lean dispatch count drift is INFORMATIVE only, not a
            # hard regression failure.  Z3's per-class UNKNOWN
            # behavior is nondeterministic across machines / runs;
            # CI may decide classes that locally Lean had to dispatch,
            # or vice-versa.  Soundness lives in `expected_solutions`.
            lean_note_extra = ""
            if expected_lean is not None and ld["valid"] != expected_lean:
                lean_note_extra = (
                    f" (note: Lean valid {ld['valid']} vs "
                    f"expected_lean_hits {expected_lean} — Z3 "
                    f"nondeterminism; informative only)"
                )
            timing_note = _timing_note(rel, elapsed)
            if mismatches:
                print(f"{rel:<40} SAT — {n_sols} solution(s){lean_note}  "
                      f"({elapsed:.1f}s){timing_note} — MISMATCH: "
                      + "; ".join(mismatches))
                fail += 1
            else:
                annot_bits = []
                if expected is not None:
                    annot_bits.append("counts match")
                print(f"{rel:<40} SAT — {n_sols} solution(s)"
                      f"{lean_note}"
                      + (f", {', '.join(annot_bits)}" if annot_bits else "")
                      + f"{lean_note_extra}"
                      + f"  ({elapsed:.1f}s){timing_note}")
                ok += 1
        elif rt == "NoSolution":
            print(f"{rel:<40} UNSAT — {payload.get('reason', '?')}  "
                  f"({elapsed:.1f}s)")
            fail += 1
        elif rt == "Timeout":
            note = " (subprocess timeout)" if payload.get(
                "subprocess_timeout") else ""
            print(f"{rel:<40} TIMEOUT{note}  ({elapsed:.1f}s)")
            fail += 1
        else:
            print(f"{rel:<40} UNKNOWN_RESULT_TYPE ({rt})  "
                  f"({elapsed:.1f}s)")
            fail += 1

    # Also run the failure-channel test (cheap, in-process — it tests
    # NoSolution/Timeout reporting machinery, not a benchmark, so the
    # subprocess isolation argument doesn't apply).
    print()
    print("─── failure-channel test ───")
    failure_test_path = repo_root / "tests" / "test_failure_channels.py"
    spec = importlib.util.spec_from_file_location("_fctest", failure_test_path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    try:
        spec.loader.exec_module(mod)
        ok += 1
    except Exception as e:
        print(f"failure-channel test FAILED: {e}")
        fail += 1

    # Timing-drift summary.  All soft (don't affect fail count) —
    # CI may have a different baseline machine, so this is for the
    # developer running locally.  Update tests/regression_timings.json
    # when changes are intentional.
    if slow_drifts or fast_drifts or missing_baseline:
        print()
        print("─── timing drift (soft, informational) ───")
        for rel, baseline, current in slow_drifts:
            print(f"  SLOW  {rel}: {current:.1f}s vs baseline {baseline:.1f}s "
                  f"({current/baseline:.1f}x)")
        for rel, baseline, current in fast_drifts:
            print(f"  FAST  {rel}: {current:.1f}s vs baseline {baseline:.1f}s "
                  f"({current/baseline:.1f}x — consider updating baseline)")
        if missing_baseline:
            print(f"  Missing baseline ({len(missing_baseline)}): "
                  + ", ".join(missing_baseline[:5])
                  + (" ..." if len(missing_baseline) > 5 else ""))

    print()
    print(f"{ok} passed, {fail} failed")
    return fail


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--slow", action="store_true",
                    help="include slow (axiom-heavy) benchmarks")
    ap.add_argument("--stretch", action="store_true",
                    help="run ONLY the Phase X.S stretch suite "
                    "(disjoint from quick/slow; see RESEARCH.md §D.1.5)")
    args = ap.parse_args()

    if args.stretch:
        return run(list(STRETCH))

    suite = list(QUICK)
    if args.slow:
        suite += SLOW
    return run(suite)


if __name__ == "__main__":
    sys.exit(main())
