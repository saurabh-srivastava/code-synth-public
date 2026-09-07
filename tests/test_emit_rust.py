"""tests/test_emit_rust.py — Rust emitter validation.

For each benchmark: synthesize, emit Rust, wrap in a `fn main()`
driver that exercises the function, compile with `rustc`, run the
binary, assert stdout matches.  Same shape as `tests/test_emit_c.py`.

A 15s runtime timeout guards against synthesizer bugs producing
unsound code that infinite-loops at runtime.
"""
from __future__ import annotations
import importlib.util
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

# Tests skip cleanly if rustc isn't available; CI installs it.
_RUSTC = shutil.which("rustc") or os.path.expanduser("~/.cargo/bin/rustc")
_HAS_RUSTC = os.path.exists(_RUSTC) and os.access(_RUSTC, os.X_OK)


def _load_problem(rel_path: str):
    spec = importlib.util.spec_from_file_location("_bench", REPO / rel_path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _emit_and_check(rel_path: str,
                   fname: str,
                   driver: str,
                   expected: str) -> None:
    """Synthesize + emit Rust + wrap in driver + compile + run."""
    if not _HAS_RUSTC:
        print(f"  SKIP — rustc not found at {_RUSTC}")
        return

    from synth import solve, emit_rust
    problem = _load_problem(rel_path)
    result = solve(problem)
    assert result, f"{rel_path}: synthesis failed"

    code = emit_rust(result.best, problem, fname=fname)
    full = code + "\n\n" + driver

    workdir = Path("/tmp") / f"_synth_rust_{fname}"
    workdir.mkdir(exist_ok=True)
    src = workdir / f"{fname}.rs"
    binp = workdir / fname
    src.write_text(full)

    cc = subprocess.run(
        [_RUSTC, "-O", str(src), "-o", str(binp),
         "--edition", "2021"],
        capture_output=True, text=True,
    )
    assert cc.returncode == 0, (
        f"{rel_path}: rustc failed\n"
        f"stderr:\n{cc.stderr}\n"
        f"source:\n{full}"
    )

    try:
        run = subprocess.run([str(binp)], capture_output=True,
                             text=True, timeout=15)
    except subprocess.TimeoutExpired:
        raise AssertionError(
            f"{rel_path}: binary timed out after 15s — likely a synthesizer "
            f"soundness bug producing infinite-looping code"
        )
    assert run.returncode == 0, (
        f"{rel_path}: binary exit {run.returncode}\n"
        f"stderr:\n{run.stderr}"
    )
    assert run.stdout == expected, (
        f"{rel_path}: stdout mismatch\n"
        f"expected:\n{expected!r}\n"
        f"got:\n{run.stdout!r}"
    )


def test_intsqrt() -> None:
    driver = """
fn main() {
    println!("{}", intsqrt(25));
    println!("{}", intsqrt(99));
    println!("{}", intsqrt(1));
}
"""
    _emit_and_check("benchmarks/intsqrt.py", "intsqrt", driver,
                    "6\n10\n2\n")


def test_sumi() -> None:
    driver = """
fn main() {
    println!("{}", sumi(5));
    println!("{}", sumi(10));
    println!("{}", sumi(0));
}
"""
    _emit_and_check("benchmarks/sumi.py", "sumi", driver,
                    "15\n55\n0\n")


def test_intdiv() -> None:
    driver = """
fn main() {
    let (q, r) = intdiv(17, 5);
    println!("{} {}", q, r);
    let (q, r) = intdiv(100, 7);
    println!("{} {}", q, r);
}
"""
    _emit_and_check("benchmarks/intdiv.py", "intdiv", driver,
                    "3 2\n14 2\n")


def test_abs() -> None:
    driver = """
fn main() {
    println!("{}", abs_proc(-7));
    println!("{}", abs_proc(0));
    println!("{}", abs_proc(42));
}
"""
    _emit_and_check("benchmarks/abs.py", "abs_proc", driver,
                    "7\n0\n42\n")


def test_swap() -> None:
    driver = """
fn main() {
    let (x, y) = swap(10, 20, 10, 20);
    println!("{} {}", x, y);
}
"""
    _emit_and_check("benchmarks/swap.py", "swap", driver,
                    "20 10\n")


def test_array_zero() -> None:
    driver = """
fn main() {
    let mut A: Vec<i64> = vec![1, 2, 3, 4, 5];
    array_zero(&mut A, 5);
    for k in 0..5 {
        print!("{} ", A[k]);
    }
    println!();
}
"""
    _emit_and_check("benchmarks/array_zero.py", "array_zero", driver,
                    "0 0 0 0 0 \n")


def test_bubble_sort() -> None:
    driver = """
fn main() {
    let mut A: Vec<i64> = vec![5, 3, 8, 1, 9, 2, 7];
    bubble_sort(7, &mut A);
    for k in 0..7 {
        print!("{} ", A[k]);
    }
    println!();
}
"""
    _emit_and_check("benchmarks/bubble_sort.py", "bubble_sort", driver,
                    "1 2 3 5 7 8 9 \n")


def test_insertion_sort() -> None:
    driver = """
fn main() {
    let mut A: Vec<i64> = vec![5, 3, 8, 1, 9, 2, 7];
    insertion_sort(7, &mut A);
    for k in 0..7 {
        print!("{} ", A[k]);
    }
    println!();
}
"""
    _emit_and_check("benchmarks/insertion_sort.py", "insertion_sort",
                    driver, "1 2 3 5 7 8 9 \n")


def test_rec_const() -> None:
    driver = """
fn main() {
    println!("{}", rec_const(0));
    println!("{}", rec_const(5));
    println!("{}", rec_const(20));
}
"""
    _emit_and_check("benchmarks/rec_const.py", "rec_const", driver,
                    "0\n0\n0\n")


def test_rec_neg() -> None:
    driver = """
fn main() {
    println!("{}", rec_neg(0));
    println!("{}", rec_neg(5));
    println!("{}", rec_neg(10));
}
"""
    _emit_and_check("benchmarks/rec_neg.py", "rec_neg", driver,
                    "0\n-5\n-10\n")


def test_rec_zero_array() -> None:
    driver = """
fn main() {
    let mut A: Vec<i64> = vec![1, 2, 3, 4, 5];
    rec_zero_array(&mut A, 5);
    for k in 0..5 {
        print!("{} ", A[k]);
    }
    println!();
}
"""
    _emit_and_check("benchmarks/rec_zero_array.py", "rec_zero_array",
                    driver, "0 0 0 0 0 \n")


def test_matrix_init() -> None:
    """2D int[][] in-place via &mut [Vec<i64>]: zero-fills 3×4
    initialized to 7s, verifies cell-sum is 0."""
    driver = """
fn main() {
    let mut a: Vec<Vec<i64>> = vec![vec![7; 4]; 3];
    matrix_init(3, 4, &mut a);
    let sum: i64 = a.iter().map(|row| row.iter().sum::<i64>()).sum();
    println!("{}", sum);
}
"""
    _emit_and_check("benchmarks/matrix_init.py", "matrix_init",
                    driver, "0\n")


if __name__ == "__main__":
    if not _HAS_RUSTC:
        print(f"rustc not found at {_RUSTC} — skipping all tests")
        sys.exit(0)
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
