"""tests/test_helper_codegen.py — §H.2 codegen helper-citation path.

Exercises `synth.lean_backend.codegen` end-to-end:
  1. Take a benchmark with a `helper_registry` set.
  2. Construct chosen_atoms that match the registry's required atoms.
  3. Call `verify_class_via_lean`.
  4. Assert v.is_valid AND v.via_helper (proves the citation fired).

Skips cleanly when `lake` is not available.

Acts as the smoke test for `Verdict.via_helper` propagation, the
`_substitute_proof_body` substitution, and the registry-matcher.
"""
from __future__ import annotations
import importlib.util
import os
import shutil
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

_LAKE = shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
_HAS_LAKE = os.path.exists(_LAKE) and os.access(_LAKE, os.X_OK)


def _load_benchmark(name: str):
    """Import a benchmark module by file path."""
    path = REPO / "benchmarks" / "stretch" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_floyd_warshall_post_from_inv_cites_helper():
    """FW bundle-post obligation must dispatch via Tier-3 helper.

    Constructs the chosen_atoms = full τ@L0 (including the
    required atoms 1 and 3 — k_le_n and outer-table-filled).
    Calls verify_class_via_lean for sc_kind=safety-bundle-post,
    loop_id=L0.  Asserts:
      - v.is_valid (Lean closed the obligation).
      - v.via_helper (the citation fired, not generic tactics).
      - elapsed ≤ 15s (sanity: the fast path is fast).
    """
    if not _HAS_LAKE:
        print("test_floyd_warshall_post_from_inv_cites_helper: SKIP (no lake)")
        return

    fw = _load_benchmark("floyd_warshall")
    problem = fw.PROBLEM
    # Translator helpers walk problem.template looking for loop_id;
    # IDs are assigned by expand().  Solver runs expand first; we
    # mirror that here since we're calling verify directly.
    from synth.expand import expand
    expand(problem)

    # Full τ@L0 — includes all required atoms 1 and 3 by construction.
    chosen_atoms = {
        "tau@L0": list(problem.atoms["tau@L0"]),
        "g@L0": problem.atoms["g@L0"][0],
        "phi@L0": problem.atoms["phi@L0"][0],
        # Init/skip SBs — chain-bundle translator reads these.
        "s@B0": problem.atoms["s@B0"][0],
        "s@B5": problem.atoms["s@B5"][0],
    }

    from synth.lean_backend.verify import verify_class_via_lean

    t0 = time.monotonic()
    v = verify_class_via_lean(
        problem,
        chosen_atoms,
        sc_kind="safety-bundle-post",
        loop_id="L0",
        theorem_name="test_fw_post_helper",
        timeout_s=30.0,
    )
    elapsed = time.monotonic() - t0

    assert v.via_helper, (
        f"helper-citation path did NOT fire — v.via_helper={v.via_helper}; "
        f"v.status={v.status}; detail={v.detail!r}; elapsed={elapsed:.1f}s"
    )
    assert v.is_valid, (
        f"helper citation didn't close — v.status={v.status}; "
        f"detail={v.detail!r}; elapsed={elapsed:.1f}s"
    )
    # 30s is generous; first call may incur olean warmup.  Subsequent
    # calls in the same process should be <5s.
    assert elapsed <= 30.0, (
        f"helper-citation path too slow: {elapsed:.1f}s (expected ≤30s)"
    )
    print(f"test_floyd_warshall_post_from_inv_cites_helper: PASS "
          f"({elapsed:.1f}s, via_helper={v.via_helper})")


def test_no_registry_falls_through():
    """A Problem without `helper_registry` must NOT set via_helper.

    Uses sumi (no helper registry); verifies via_helper=False on a
    valid obligation.
    """
    if not _HAS_LAKE:
        print("test_no_registry_falls_through: SKIP (no lake)")
        return

    import importlib.util
    sumi_path = REPO / "benchmarks" / "sumi.py"
    spec = importlib.util.spec_from_file_location("sumi", sumi_path)
    sumi = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(sumi)
    problem = sumi.PROBLEM
    assert problem.helper_registry is None, "sumi shouldn't have a registry"

    from synth import solve
    result = solve(problem)
    assert bool(result), f"sumi failed to solve: {result}"
    sol = result.solutions[0]

    from synth.lean_backend.verify import verify_class_via_lean
    chosen_atoms = sol.atoms
    v = verify_class_via_lean(
        problem, chosen_atoms,
        sc_kind="ranking-lb", loop_id="L0",
        theorem_name="test_sumi_no_helper",
        timeout_s=15.0,
    )
    assert not v.via_helper, (
        f"no-registry case has via_helper=True (should be False)"
    )
    assert v.is_valid, f"sumi ranking-lb didn't close: {v}"
    print(f"test_no_registry_falls_through: PASS "
          f"(via_helper={v.via_helper}, status={v.status})")


def _generic_post_from_inv_test(bench: str, theorem_label: str):
    """Shared smoke check: full τ chosen → bundle-post via helper.

    For single-loop benchmarks (kadane / majority / modular_exp) —
    asserts v.via_helper=True and v.is_valid.  Lets us validate
    all three ports with one body.
    """
    if not _HAS_LAKE:
        print(f"_{bench}_via_helper: SKIP (no lake)")
        return
    fw_path = REPO / "benchmarks" / "stretch" / f"{bench}.py"
    spec = importlib.util.spec_from_file_location(bench, fw_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    problem = mod.PROBLEM
    from synth.expand import expand
    expand(problem)
    chosen = {}
    for hid, alist in problem.atoms.items():
        if hid.startswith("tau@"):
            chosen[hid] = list(alist)
        else:
            chosen[hid] = alist[0]
    from synth.lean_backend.verify import verify_class_via_lean
    t0 = time.monotonic()
    v = verify_class_via_lean(
        problem, chosen,
        sc_kind="safety-bundle-post", loop_id="L0",
        theorem_name=theorem_label, timeout_s=30.0,
    )
    elapsed = time.monotonic() - t0
    assert v.via_helper, (
        f"{bench}: helper-citation path did NOT fire — "
        f"v.via_helper={v.via_helper}; status={v.status}; "
        f"detail={v.detail!r}; elapsed={elapsed:.1f}s"
    )
    assert v.is_valid, (
        f"{bench}: helper citation didn't close — "
        f"status={v.status}; detail={v.detail!r}; elapsed={elapsed:.1f}s"
    )
    print(f"{bench}_via_helper: PASS "
          f"({elapsed:.1f}s, via_helper={v.via_helper})")


def test_kadane_post_from_inv_cites_helper():
    _generic_post_from_inv_test("kadane_max_subarray",
                                "test_kadane_post_helper")


def test_majority_post_from_inv_cites_helper():
    _generic_post_from_inv_test("majority_element",
                                "test_majority_post_helper")


def test_modexp_post_from_inv_cites_helper():
    _generic_post_from_inv_test("modular_exponentiation",
                                "test_modexp_post_helper")


if __name__ == "__main__":
    print("Running test_helper_codegen.py tests...")
    test_no_registry_falls_through()
    test_floyd_warshall_post_from_inv_cites_helper()
    test_kadane_post_from_inv_cites_helper()
    test_majority_post_from_inv_cites_helper()
    test_modexp_post_from_inv_cites_helper()
    print("All tests passed.")
