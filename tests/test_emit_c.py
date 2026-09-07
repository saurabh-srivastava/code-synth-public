"""tests/test_emit_c.py — verify the C emitter produces compilable
code for representative benchmarks, and that the compiled functions
return the expected values on hand-picked inputs.

Strategy: for each benchmark, synthesize, emit C, wrap in a main()
driver that calls the function with sample inputs and prints results,
compile with `clang`, run, and check stdout.

Compilation alone is the load-bearing test — runtime correctness
checks below are tiny smoke tests, not exhaustive coverage.
"""
from __future__ import annotations
import importlib.util
import os
import subprocess
import sys
import tempfile
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent


def _load_problem(bench_path: str):
    spec = importlib.util.spec_from_file_location("_bench", bench_path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _emit_and_check(bench: str, driver_main: str, expected: str) -> None:
    """Synthesize bench, emit C, append driver_main, compile + run,
    assert stdout == expected."""
    sys.path.insert(0, str(REPO))
    from synth import solve, emit_c

    problem = _load_problem(str(REPO / "benchmarks" / f"{bench}.py"))
    result = solve(problem)
    assert result, f"{bench}: synthesis failed"

    c_code = emit_c(result.best, problem, fname=bench)
    full = "#include <stdio.h>\n\n" + c_code + "\n\n" + driver_main

    with tempfile.TemporaryDirectory() as d:
        cpath = Path(d) / f"{bench}.c"
        epath = Path(d) / bench
        cpath.write_text(full)
        cp = subprocess.run(
            ["clang", "-Wall", "-Werror", "-o", str(epath), str(cpath)],
            capture_output=True, text=True,
        )
        assert cp.returncode == 0, (
            f"{bench} compile failed:\n"
            f"--- C ---\n{full}\n--- stderr ---\n{cp.stderr}"
        )
        try:
            rp = subprocess.run(
                [str(epath)], capture_output=True, text=True, timeout=15,
            )
        except subprocess.TimeoutExpired:
            raise AssertionError(
                f"{bench}: compiled binary infinite-looped (15s timeout) — "
                f"likely an unsound synthesized solution.\n"
                f"--- C ---\n{full}"
            )
        assert rp.returncode == 0, f"{bench} run failed: {rp.stderr}"
        assert rp.stdout == expected, (
            f"{bench}: expected {expected!r}, got {rp.stdout!r}\n"
            f"C:\n{full}"
        )


def test_intsqrt() -> None:
    driver = """
int main(void) {
    printf("%d\\n", intsqrt(25));
    printf("%d\\n", intsqrt(99));
    return 0;
}
"""
    # intsqrt(x) returns the smallest i with (i-1)^2 <= x < i^2.
    # For x=25 (= 5^2): need x < i^2, so i ≥ 6, and 5^2 = 25 ≤ 25 ✓ → i=6.
    # For x=99: 9^2 = 81 ≤ 99 < 100 = 10^2 → i=10.
    _emit_and_check("intsqrt", driver, "6\n10\n")


def test_sumi() -> None:
    driver = """
int main(void) {
    printf("%d\\n", sumi(5));
    printf("%d\\n", sumi(10));
    return 0;
}
"""
    # sumi(N) = N*(N+1)/2.  sumi(5) = 15, sumi(10) = 55.
    _emit_and_check("sumi", driver, "15\n55\n")


def test_intdiv() -> None:
    driver = """
int main(void) {
    int q, r;
    intdiv(17, 5, &q, &r);
    printf("%d %d\\n", q, r);
    intdiv(100, 7, &q, &r);
    printf("%d %d\\n", q, r);
    return 0;
}
"""
    _emit_and_check("intdiv", driver, "3 2\n14 2\n")


def test_abs() -> None:
    driver = """
int main(void) {
    printf("%d\\n", abs(-7));
    printf("%d\\n", abs(0));
    printf("%d\\n", abs(42));
    return 0;
}
"""
    _emit_and_check("abs", driver, "7\n0\n42\n")


def test_array_zero() -> None:
    driver = """
int main(void) {
    int A[5] = {1, 2, 3, 4, 5};
    array_zero(A, 5);
    for (int k = 0; k < 5; k++) printf("%d ", A[k]);
    printf("\\n");
    return 0;
}
"""
    _emit_and_check("array_zero", driver, "0 0 0 0 0 \n")


def test_bubble_sort() -> None:
    driver = """
int main(void) {
    int A[7] = {5, 3, 8, 1, 9, 2, 7};
    bubble_sort(7, A);
    for (int k = 0; k < 7; k++) printf("%d ", A[k]);
    printf("\\n");
    return 0;
}
"""
    _emit_and_check("bubble_sort", driver, "1 2 3 5 7 8 9 \n")


def test_insertion_sort() -> None:
    driver = """
int main(void) {
    int A[7] = {5, 3, 8, 1, 9, 2, 7};
    insertion_sort(7, A);
    for (int k = 0; k < 7; k++) printf("%d ", A[k]);
    printf("\\n");
    return 0;
}
"""
    _emit_and_check("insertion_sort", driver, "1 2 3 5 7 8 9 \n")


def test_rec_const() -> None:
    driver = """
int main(void) {
    printf("%d\\n", rec_const(0));
    printf("%d\\n", rec_const(5));
    printf("%d\\n", rec_const(20));
    return 0;
}
"""
    # Post: result == 0.  Every sound solution returns 0 (or n=0 for
    # the base case which is still 0 when n==0).
    _emit_and_check("rec_const", driver, "0\n0\n0\n")


def test_rec_neg() -> None:
    driver = """
int main(void) {
    printf("%d\\n", rec_neg(0));
    printf("%d\\n", rec_neg(3));
    printf("%d\\n", rec_neg(7));
    return 0;
}
"""
    # Post: result == 0 - n.
    _emit_and_check("rec_neg", driver, "0\n-3\n-7\n")


def test_rec_zero_array() -> None:
    driver = """
int main(void) {
    int A[5] = {1, 2, 3, 4, 5};
    rec_zero_array(A, 5);
    for (int k = 0; k < 5; k++) printf("%d ", A[k]);
    printf("\\n");
    int B[0];
    rec_zero_array(B, 0);  /* n=0 base case — no-op */
    printf("done\\n");
    return 0;
}
"""
    _emit_and_check("rec_zero_array", driver, "0 0 0 0 0 \ndone\n")


def test_max_array() -> None:
    """max_array's post `∀k. A[k] ≤ m` is underspecified (REC 5) so
    multiple sound solutions exist with different output for some
    inputs (e.g. m=0 initialization gives 0 for all-negative arrays
    even though that's a valid upper bound).  Test on an
    all-positive input where every sound solution converges to the
    true max — and assert termination + correctness on the BEST
    (score-minimum) solution.

    A subtler reason to keep this test: it was the one that
    surfaced the SB-in-Loop-body coverage bug (sol#0 with non-
    covering guards `A[i] < m ∨ A[i] <= m` infinite-looped at
    runtime).  Keeping the test guards against regression of that
    fix.
    """
    driver = """
int main(void) {
    int A[5] = {3, 1, 4, 1, 5};
    printf("%d\\n", max_array(A, 5));
    int C[1] = {42};
    printf("%d\\n", max_array(C, 1));
    return 0;
}
"""
    _emit_and_check("max_array", driver, "5\n42\n")


def test_matrix_init() -> None:
    """2D int[][] in-place: synth matrix_init, allocate a 3×4 row-
    pointer array initialized to 7s, run, verify all cells are 0."""
    driver = """
int main(void) {
    int r0[4] = {7, 7, 7, 7};
    int r1[4] = {7, 7, 7, 7};
    int r2[4] = {7, 7, 7, 7};
    int *A[3] = {r0, r1, r2};
    matrix_init(3, 4, A);
    int sum = 0;
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 4; j++) sum += A[i][j];
    printf("%d\\n", sum);
    return 0;
}
"""
    _emit_and_check("matrix_init", driver, "0\n")


if __name__ == "__main__":
    # Run all test functions in module order; print PASS/FAIL.
    import time
    tests = [(name, fn) for name, fn in globals().items()
             if name.startswith("test_") and callable(fn)]
    failures = 0
    for name, fn in tests:
        t = time.monotonic()
        try:
            fn()
            print(f"{name:<25} PASS  ({time.monotonic()-t:.1f}s)")
        except AssertionError as e:
            print(f"{name:<25} FAIL  ({time.monotonic()-t:.1f}s)")
            print(f"    {e}")
            failures += 1
    print()
    print(f"{len(tests)-failures} passed, {failures} failed")
    sys.exit(failures)
