"""tests/test_emit_py.py — Python emitter validation.

For each benchmark: synthesize, emit Python in both modes
(`runtime_check=False` and `=True`), `exec` the generated source,
call the synthesized function on sample inputs, check output.  In
`runtime_check=True` mode the emitted code self-validates pre /
invariants / decrease / lower-bound / post / coverage at every step;
a `ProofViolation` from those calls would mean the synthesized
program doesn't actually satisfy its own proof — i.e., a soundness
bug in the synthesizer or a translation bug in the emitter.

Each test also includes a "deliberate violation" check (where
applicable): pass an input that violates `Pre` and verify the
runtime check catches it.
"""
from __future__ import annotations
import importlib.util
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))


def _load_problem(rel_path: str):
    spec = importlib.util.spec_from_file_location("_bench", REPO / rel_path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _emit_and_run(rel_path: str, fname: str, *,
                  runtime_check: bool) -> tuple[str, dict]:
    """Synthesize the benchmark, emit Python, exec into a namespace,
    return (source, namespace).  The namespace has the synthesized
    function at ns[fname]."""
    from synth import solve, emit_py
    problem = _load_problem(rel_path)
    result = solve(problem)
    assert result, f"{rel_path}: synthesis failed"
    code = emit_py(result.best, problem, fname=fname,
                   runtime_check=runtime_check)
    ns: dict = {}
    exec(compile(code, f"<{fname}>", "exec"), ns)
    assert fname in ns, f"emitter didn't define {fname}"
    return code, ns


def test_intsqrt_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/intsqrt.py", "intsqrt",
                          runtime_check=False)
    assert ns["intsqrt"](25) == 6
    assert ns["intsqrt"](99) == 10
    assert ns["intsqrt"](1)  == 2


def test_intsqrt_runtime_check() -> None:
    _, ns = _emit_and_run("benchmarks/intsqrt.py", "intsqrt",
                          runtime_check=True)
    assert ns["intsqrt"](25) == 6
    assert ns["intsqrt"](99) == 10
    # Violating Pre `x >= 1` should raise.
    from synth.proof_runtime import ProofViolation
    try:
        ns["intsqrt"](0)
        raise AssertionError("expected ProofViolation on Pre violation")
    except ProofViolation as e:
        assert e.kind == "pre", f"expected pre violation, got {e.kind}"


def test_sumi_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/sumi.py", "sumi",
                          runtime_check=False)
    assert ns["sumi"](5) == 15
    assert ns["sumi"](10) == 55
    assert ns["sumi"](0) == 0


def test_sumi_runtime_check() -> None:
    _, ns = _emit_and_run("benchmarks/sumi.py", "sumi",
                          runtime_check=True)
    assert ns["sumi"](5) == 15
    assert ns["sumi"](10) == 55


def test_intdiv_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/intdiv.py", "intdiv",
                          runtime_check=False)
    assert ns["intdiv"](17, 5) == (3, 2)
    assert ns["intdiv"](100, 7) == (14, 2)


def test_intdiv_runtime_check() -> None:
    _, ns = _emit_and_run("benchmarks/intdiv.py", "intdiv",
                          runtime_check=True)
    assert ns["intdiv"](17, 5) == (3, 2)
    from synth.proof_runtime import ProofViolation
    # Pre is `y > 0 and x >= 0`.  y=0 should trip it.
    try:
        ns["intdiv"](10, 0)
        raise AssertionError("expected ProofViolation on Pre")
    except ProofViolation as e:
        assert e.kind == "pre"


def test_abs_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/abs.py", "abs_proc",
                          runtime_check=False)
    assert ns["abs_proc"](-7) == 7
    assert ns["abs_proc"](0) == 0
    assert ns["abs_proc"](42) == 42


def test_abs_runtime_check() -> None:
    _, ns = _emit_and_run("benchmarks/abs.py", "abs_proc",
                          runtime_check=True)
    assert ns["abs_proc"](-7) == 7
    assert ns["abs_proc"](42) == 42


def test_array_zero_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/array_zero.py", "array_zero",
                          runtime_check=False)
    A = [1, 2, 3, 4, 5]
    ns["array_zero"](A, 5)
    assert A == [0, 0, 0, 0, 0]


def test_array_zero_runtime_check() -> None:
    """The quantified post `∀k. 0 ≤ k < n ⇒ A[k] == 0` self-checks."""
    _, ns = _emit_and_run("benchmarks/array_zero.py", "array_zero",
                          runtime_check=True)
    A = [1, 2, 3, 4, 5]
    ns["array_zero"](A, 5)
    assert A == [0, 0, 0, 0, 0]


def test_bubble_sort_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/bubble_sort.py", "bubble_sort",
                          runtime_check=False)
    A = [5, 3, 8, 1, 9, 2, 7]
    ns["bubble_sort"](7, A)
    assert A == [1, 2, 3, 5, 7, 8, 9]


def test_bubble_sort_runtime_check() -> None:
    """The bilateral quantified post (∀p, q. ... ⇒ ...) self-checks."""
    _, ns = _emit_and_run("benchmarks/bubble_sort.py", "bubble_sort",
                          runtime_check=True)
    A = [5, 3, 8, 1, 9, 2, 7]
    ns["bubble_sort"](7, A)
    assert A == [1, 2, 3, 5, 7, 8, 9]


def test_matrix_init_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/matrix_init.py", "matrix_init",
                          runtime_check=False)
    A = [[1, 2, 3], [4, 5, 6]]
    ns["matrix_init"](2, 3, A)
    assert A == [[0, 0, 0], [0, 0, 0]]


def test_matrix_init_runtime_check() -> None:
    """First 2D-array benchmark (Phase 3.S framework extension).
    Validates that `Update(A, i, j, v)` decodes to `A[i][j] = v` and
    `A[p][q]` reads work end-to-end."""
    _, ns = _emit_and_run("benchmarks/matrix_init.py", "matrix_init",
                          runtime_check=True)
    A = [[1, 2, 3], [4, 5, 6]]
    ns["matrix_init"](2, 3, A)
    assert A == [[0, 0, 0], [0, 0, 0]]


def test_insertion_sort_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/insertion_sort.py", "insertion_sort",
                          runtime_check=False)
    A = [5, 3, 8, 1, 9, 2, 7]
    ns["insertion_sort"](7, A)
    assert A == [1, 2, 3, 5, 7, 8, 9]


def test_insertion_sort_runtime_check() -> None:
    """Three quantified τ_inner atoms (left sorted / right sorted / wall LB)
    plus the bilateral quantified post all self-check at runtime."""
    _, ns = _emit_and_run("benchmarks/insertion_sort.py", "insertion_sort",
                          runtime_check=True)
    A = [5, 3, 8, 1, 9, 2, 7]
    ns["insertion_sort"](7, A)
    assert A == [1, 2, 3, 5, 7, 8, 9]


def test_max_array_no_check() -> None:
    _, ns = _emit_and_run("benchmarks/max_array.py", "max_array",
                          runtime_check=False)
    A = [3, 1, 4, 1, 5]
    m = ns["max_array"](A, 5)
    assert all(a <= m for a in A), f"m={m} not an upper bound of {A}"


def test_max_array_runtime_check() -> None:
    """The synthesizer's ranking-decrease check must reliably reject
    `phi = i` (INCREASING) regardless of Z3 quantifier-instantiation
    nondeterminism.  Used to be a known-flaky test before P2 landed
    (synth/solver.py — treat UNKNOWN as REJECT for ranking-family
    constraints).  Now back online as a soundness regression guard.
    """
    _, ns = _emit_and_run("benchmarks/max_array.py", "max_array",
                          runtime_check=True)
    A = [3, 1, 4, 1, 5]
    m = ns["max_array"](A, 5)
    assert all(a <= m for a in A), f"m={m} not an upper bound of {A}"


def test_swap_no_check() -> None:
    """swap is acyclic; tests parallel-assignment emission."""
    _, ns = _emit_and_run("benchmarks/swap.py", "swap",
                          runtime_check=False)
    # Signature is swap(x, y, c1, c2) -> tuple[int, int]
    out = ns["swap"](10, 20, 10, 20)
    assert out == (20, 10), f"expected (20, 10), got {out}"


if __name__ == "__main__":
    tests = [(n, fn) for n, fn in globals().items()
             if n.startswith("test_") and callable(fn)]
    fails = 0
    for name, fn in tests:
        t = time.monotonic()
        try:
            fn()
            print(f"{name:<40} PASS  ({time.monotonic() - t:.1f}s)")
        except AssertionError as e:
            print(f"{name:<40} FAIL  ({time.monotonic() - t:.1f}s)")
            print(f"    {e}")
            fails += 1
        except Exception as e:
            print(f"{name:<40} ERROR ({time.monotonic() - t:.1f}s)")
            print(f"    {type(e).__name__}: {e}")
            fails += 1
    print()
    print(f"{len(tests) - fails} passed, {fails} failed")
    sys.exit(fails)
