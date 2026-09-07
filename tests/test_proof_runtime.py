"""tests/test_proof_runtime.py — exercise the runtime proof check
library used by the Python emitter.

Each test verifies (a) that the check passes silently when the
obligation holds, and (b) that it raises `ProofViolation` with the
expected `kind` and useful diagnostic when violated.
"""
from __future__ import annotations
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from synth.proof_runtime import (
    ProofViolation,
    proof_check,
    proof_pre,
    proof_post,
    proof_invariant,
    proof_decrease,
    proof_lower_bound,
    proof_coverage,
)


# ─────────────────────────────────────────────────────────────────────
# Generic and pre/post/invariant — same shape (cond, message).
# ─────────────────────────────────────────────────────────────────────
def test_proof_check_pass() -> None:
    proof_check(True, "trivially true")
    proof_check(1 + 1 == 2, "math")


def test_proof_check_fail() -> None:
    try:
        proof_check(False, "always false")
        raise AssertionError("expected ProofViolation")
    except ProofViolation as e:
        assert e.kind == "check"
        assert e.message == "always false"
        assert "always false" in str(e)


def test_proof_pre_pass() -> None:
    proof_pre(5 >= 0, "n >= 0")


def test_proof_pre_fail() -> None:
    try:
        proof_pre(-1 >= 0, "n >= 0")
    except ProofViolation as e:
        assert e.kind == "pre"
        assert "n >= 0" in str(e)
        return
    raise AssertionError("expected ProofViolation")


def test_proof_post_fail() -> None:
    try:
        proof_post(False, "result == 0")
    except ProofViolation as e:
        assert e.kind == "post"
        assert "result == 0" in str(e)
        return
    raise AssertionError("expected ProofViolation")


def test_proof_invariant_pass_and_fail() -> None:
    proof_invariant(True, "L0: i <= n")
    try:
        proof_invariant(False, "L0: i <= n")
    except ProofViolation as e:
        assert e.kind == "invariant"
        assert "L0: i <= n" in str(e)


# ─────────────────────────────────────────────────────────────────────
# Decrease — takes (curr, prev, message); strict decrease required.
# ─────────────────────────────────────────────────────────────────────
def test_proof_decrease_pass() -> None:
    proof_decrease(4, 5, "L0 phi")           # 4 < 5  ✓
    proof_decrease(-1, 0, "L0 phi")          # works across zero


def test_proof_decrease_equal_fails() -> None:
    """Strict decrease, not <=."""
    try:
        proof_decrease(5, 5, "L0 phi")
    except ProofViolation as e:
        assert e.kind == "decrease"
        s = str(e)
        assert "prev=5" in s
        assert "curr=5" in s
        return
    raise AssertionError("expected ProofViolation on equal phi")


def test_proof_decrease_increase_fails() -> None:
    try:
        proof_decrease(6, 5, "L0 phi")
    except ProofViolation as e:
        assert e.kind == "decrease"
        assert "prev=5" in str(e)
        assert "curr=6" in str(e)
        return
    raise AssertionError("expected ProofViolation on increasing phi")


# ─────────────────────────────────────────────────────────────────────
# Lower bound.
# ─────────────────────────────────────────────────────────────────────
def test_proof_lower_bound_default_bound() -> None:
    proof_lower_bound(0, "L0 phi LB")          # 0 >= 0
    proof_lower_bound(5, "L0 phi LB")
    try:
        proof_lower_bound(-1, "L0 phi LB")
    except ProofViolation as e:
        assert e.kind == "ranking-lb"
        s = str(e)
        assert "value=-1" in s and "bound=0" in s
        return
    raise AssertionError("expected ProofViolation for value < 0")


def test_proof_lower_bound_custom_bound() -> None:
    proof_lower_bound(3, "L0 phi LB", bound=3)   # 3 >= 3 ✓
    try:
        proof_lower_bound(2, "L0 phi LB", bound=3)
    except ProofViolation as e:
        s = str(e)
        assert "value=2" in s and "bound=3" in s
        return
    raise AssertionError("expected ProofViolation for value < custom bound")


# ─────────────────────────────────────────────────────────────────────
# Coverage — at least one of the supplied guards must be true.
# ─────────────────────────────────────────────────────────────────────
def test_proof_coverage_one_true() -> None:
    proof_coverage(True, False, message="B0 branch coverage")
    proof_coverage(False, False, True, message="B0 branch coverage")


def test_proof_coverage_all_false() -> None:
    try:
        proof_coverage(False, False, False, message="B0 branch coverage")
    except ProofViolation as e:
        assert e.kind == "coverage"
        assert "B0 branch coverage" in str(e)
        return
    raise AssertionError("expected ProofViolation when no guard fired")


# ─────────────────────────────────────────────────────────────────────
# ProofViolation subclasses AssertionError so existing AssertionError
# catches still work, and so pytest's assertion-introspection works.
# ─────────────────────────────────────────────────────────────────────
def test_subclass_of_assertion_error() -> None:
    try:
        proof_pre(False, "n >= 0")
    except AssertionError:
        return
    raise AssertionError("ProofViolation should be an AssertionError")


def test_violation_attributes() -> None:
    """Caller can introspect the structured attributes."""
    try:
        proof_decrease(5, 4, "phi")  # 5 >= 4, fails
    except ProofViolation as e:
        assert e.kind == "decrease"
        assert e.message == "phi"
        assert e.details == ("prev=4", "curr=5")
        return
    raise AssertionError("expected ProofViolation")


if __name__ == "__main__":
    import time
    tests = [(n, fn) for n, fn in globals().items()
             if n.startswith("test_") and callable(fn)]
    fails = 0
    for name, fn in tests:
        t = time.monotonic()
        try:
            fn()
            print(f"{name:<45} PASS  ({time.monotonic() - t:.3f}s)")
        except AssertionError as e:
            print(f"{name:<45} FAIL")
            print(f"    {e}")
            fails += 1
    print()
    print(f"{len(tests) - fails} passed, {fails} failed")
    sys.exit(fails)
