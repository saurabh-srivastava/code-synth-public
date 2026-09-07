"""Smoke tests for the multi-template harness.

Exercises:
  - Multiple variants run + aggregate.
  - Serial and parallel modes produce equivalent results.
  - Per-variant timing + status capture.
  - .best ranking selects the lowest-scoring success.
"""
from __future__ import annotations
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from synth import Problem, SB, Loop, Var
from synth.multi_template import (
    multi_template_solve,
    MultiTemplateResult,
    VariantResult,
)


def _sumi_count_up() -> Problem:
    return Problem(
        template = SB() >> Loop(SB()) >> SB(),
        inputs   = [Var("N", "int", "input")],
        outputs  = [Var("s", "int", "output")],
        locals   = [Var("i", "int", "local")],
        pre      = "N >= 0",
        post     = "2*s == N*(N + 1)",
        atoms    = {
            "tau@L0": ["2*s == i*(i + 1)", "0 <= i", "i <= N"],
            "g@L0":   ["i < N"],
            "phi@L0": ["N - i"],
            "s@B0":   [{"s": "0", "i": "0"}],
            "s@B1":   [{"s": "s + i + 1", "i": "i + 1"}],
            "s@B2":   [{"s": "s"}],
        },
    )


def _sumi_count_down() -> Problem:
    return Problem(
        template = SB() >> Loop(SB()) >> SB(),
        inputs   = [Var("N", "int", "input")],
        outputs  = [Var("s", "int", "output")],
        locals   = [Var("i", "int", "local")],
        pre      = "N >= 0",
        post     = "2*s == N*(N + 1)",
        atoms    = {
            "tau@L0": ["2*s == (N - i)*(N + i + 1)", "0 <= i", "i <= N"],
            "g@L0":   ["i > 0"],
            "phi@L0": ["i"],
            "s@B0":   [{"s": "0", "i": "N"}],
            "s@B1":   [{"s": "s + i", "i": "i - 1"}],
            "s@B2":   [{"s": "s"}],
        },
    )


def test_serial_two_variants() -> None:
    r = multi_template_solve(
        variants=[("up", _sumi_count_up()), ("down", _sumi_count_down())],
        parallel=False,
    )
    assert isinstance(r, MultiTemplateResult)
    assert len(r.variants) == 2
    assert all(v.status == "success" for v in r.variants)
    # Both should yield solutions; scores differ (different atoms).
    assert r.variants[0].score is not None
    assert r.variants[1].score is not None


def test_parallel_two_variants() -> None:
    r = multi_template_solve(
        variants=[("up", _sumi_count_up()), ("down", _sumi_count_down())],
        parallel=True,
    )
    assert len(r.variants) == 2
    assert all(v.status == "success" for v in r.variants)


def test_ordering_preserved() -> None:
    """Input order is preserved even when variants finish in
    different parallel orders."""
    names = ["a", "b", "c", "d"]
    r = multi_template_solve(
        variants=[(n, _sumi_count_up()) for n in names],
        parallel=True,
    )
    assert [v.name for v in r.variants] == names


def test_best_picks_lowest_score() -> None:
    r = multi_template_solve(
        variants=[("up", _sumi_count_up()), ("down", _sumi_count_down())],
        parallel=False,
    )
    assert r.best is not None
    # count_up's score (with the simpler invariant 2*s == i*(i+1))
    # is the lower of the two.
    assert r.best.name == "up"


def test_bool_truthy_on_any_success() -> None:
    r = multi_template_solve(
        variants=[("up", _sumi_count_up())],
        parallel=False,
    )
    assert bool(r) is True


def test_empty_variants() -> None:
    r = multi_template_solve(variants=[], parallel=False)
    assert r.variants == []
    assert r.best is None
    assert bool(r) is False


if __name__ == "__main__":
    import time
    tests = [(n, fn) for n, fn in globals().items()
             if n.startswith("test_") and callable(fn)]
    fails = 0
    for name, fn in tests:
        t = time.monotonic()
        try:
            fn()
            print(f"{name:<40} PASS  ({time.monotonic()-t:.1f}s)")
        except AssertionError as e:
            print(f"{name:<40} FAIL  ({time.monotonic()-t:.1f}s)")
            print(f"    {e}")
            fails += 1
    print()
    print(f"{len(tests)-fails} passed, {fails} failed")
    sys.exit(fails)
