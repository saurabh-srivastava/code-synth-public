"""scratch/matrix_init_emit_demo.py — exercises 2D Update in C/Rust.

Hand-constructs matrix_init's Solution, expands, and emits via
emit_c + emit_rust to confirm 4-arg `Update(A, i, j, 0)` produces
`A[i][j] = 0` in both languages.

Also runs the resulting binaries on a 3×4 matrix and asserts every
cell becomes 0.
"""
from __future__ import annotations
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from synth import emit_c, emit_rust
from synth.expand import expand
from synth.result import Solution


def _load_problem():
    p = REPO / "benchmarks/matrix_init.py"
    spec = importlib.util.spec_from_file_location("_bench", p)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _hand_solution(problem) -> Solution:
    a = problem.atoms
    # tau atoms: pick all available (matrix_init's invariants are
    # all load-bearing for the synth verdict).
    atoms = {
        "s@B0":   a["s@B0"][0],
        "tau@L0": list(a["tau@L0"]),
        "g@L0":   a["g@L0"][0],
        "phi@L0": a["phi@L0"][0],
        "s@B1":   a["s@B1"][0],
        "tau@L1": list(a["tau@L1"]),
        "g@L1":   a["g@L1"][0],
        "phi@L1": a["phi@L1"][0],
        "s@B2":   a["s@B2"][0],
        "s@B3":   a["s@B3"][0],
    }
    return Solution(choices={}, atoms=atoms, code="", score=0)


def main() -> None:
    problem = _load_problem()
    expand(problem)
    sol = _hand_solution(problem)

    code_c = emit_c(sol, problem, fname="matrix_init")
    print("=" * 64)
    print("emit_c — 2D Update")
    print("=" * 64)
    print(code_c)
    _compile_run_c(code_c)

    code_rs = emit_rust(sol, problem, fname="matrix_init")
    print()
    print("=" * 64)
    print("emit_rust — 2D Update")
    print("=" * 64)
    print(code_rs)
    _compile_run_rust(code_rs)
    print()
    print("matrix_init emit_c + emit_rust 2D-Update — OK.")


def _compile_run_c(synth_c: str) -> None:
    driver = r"""
#include <stdio.h>
int main(void) {
    int r0[4] = {7, 7, 7, 7};
    int r1[4] = {7, 7, 7, 7};
    int r2[4] = {7, 7, 7, 7};
    int *A[3] = {r0, r1, r2};
    matrix_init(3, 4, A);
    int sum = 0;
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 4; j++)
            sum += A[i][j];
    printf("sum=%d\n", sum);
    return 0;
}
"""
    full = synth_c + "\n" + driver
    with tempfile.TemporaryDirectory() as td:
        src = f"{td}/p.c"
        out = f"{td}/p"
        with open(src, "w") as f:
            f.write(full)
        subprocess.run(["clang", "-Wall", "-Werror", "-O", src, "-o", out],
                       check=True, capture_output=True, text=True)
        r = subprocess.run([out], check=True, capture_output=True,
                           text=True, timeout=10)
    print(f"C binary stdout: {r.stdout.strip()!r}  (expect 'sum=0')")
    assert r.stdout.strip() == "sum=0", r.stdout


def _compile_run_rust(synth_rs: str) -> None:
    driver = r"""
fn main() {
    let mut a: Vec<Vec<i64>> = vec![vec![7; 4]; 3];
    matrix_init(3, 4, &mut a);
    let sum: i64 = a.iter().map(|row| row.iter().sum::<i64>()).sum();
    println!("sum={}", sum);
}
"""
    full = synth_rs + "\n" + driver
    with tempfile.TemporaryDirectory() as td:
        src = f"{td}/p.rs"
        out = f"{td}/p"
        with open(src, "w") as f:
            f.write(full)
        subprocess.run(["rustc", "-O", src, "-o", out],
                       check=True, capture_output=True, text=True)
        r = subprocess.run([out], check=True, capture_output=True,
                           text=True, timeout=10)
    print(f"Rust binary stdout: {r.stdout.strip()!r}  (expect 'sum=0')")
    assert r.stdout.strip() == "sum=0", r.stdout


if __name__ == "__main__":
    main()
