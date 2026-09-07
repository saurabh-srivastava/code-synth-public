"""scratch/pair_consec_emit_demo.py — B.3 demo (emit_py).

Hand-constructs the Solution from the chosen atoms of
`bench_pair_consecutive.py`'s synthesized verdict (from
commit 815f241's 695s synth run) and round-trips it through
`emit_py` in both modes:

  1. Default (proof obligations as comments).
  2. runtime_check=True (obligations lowered to
     `synth.proof_runtime` calls).

Then exec-loads each and runs sample inputs to confirm:
  - The synthesized algorithm produces the expected matching.
  - In runtime_check mode, the matching invariant is checked
    at every loop iteration without raising ProofViolation.

This sidesteps the 695s synth re-run — we already verified
B.1 closes; this just demonstrates the code-emission slice.
"""
from __future__ import annotations
import importlib.util
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

import subprocess
import tempfile

from synth import emit_py, emit_c, emit_rust
from synth.expand import expand
from synth.result import Solution


def _load_problem():
    p = REPO / "benchmarks/open_prbs/l16_bipartite_matching/bench_pair_consecutive.py"
    spec = importlib.util.spec_from_file_location("_bench", p)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod.PROBLEM


def _hand_solution(problem) -> Solution:
    """Reproduce commit 815f241's synthesized verdict by hand."""
    # tau@L0 picks: 0 <= i, i <= n, matching-invariant (indices 0,1,2).
    # UT (idx 3) is redundant — not in the chosen subset.
    atoms = {
        "s@B0":   problem.atoms["s@B0"][0],
        "tau@L0": [problem.atoms["tau@L0"][i] for i in (0, 1, 2)],
        "g@L0":   problem.atoms["g@L0"][0],
        "phi@L0": problem.atoms["phi@L0"][0],
        "g@B1.0": problem.atoms["g@B1.0"][0],
        "s@B1.0": problem.atoms["s@B1.0"][0],
        "g@B1.1": problem.atoms["g@B1.1"][0],
        "s@B1.1": problem.atoms["s@B1.1"][0],
    }
    choices = {
        "s@B0":   0,
        "tau@L0": [0, 1, 2],
        "g@L0":   0,
        "phi@L0": 0,
        "g@B1.0": 0,
        "s@B1.0": 0,
        "g@B1.1": 0,
        "s@B1.1": 0,
    }
    return Solution(choices=choices, atoms=atoms, code="", score=32.5)


def main() -> None:
    problem = _load_problem()
    expand(problem)   # populates block_id / loop_id on the template
    sol = _hand_solution(problem)

    # ── 1. Default (comments-only proof). ─────────────────────────
    print("=" * 64)
    print("emit_py(runtime_check=False)")
    print("=" * 64)
    code = emit_py(sol, problem, fname="pair_consec",
                   runtime_check=False)
    print(code)

    # ── 2. runtime_check=True ─────────────────────────────────────
    print("=" * 64)
    print("emit_py(runtime_check=True)")
    print("=" * 64)
    code_rc = emit_py(sol, problem, fname="pair_consec",
                      runtime_check=True)
    print(code_rc)

    # ── 3. Sample runs ────────────────────────────────────────────
    print("=" * 64)
    print("Sample runs (default mode)")
    print("=" * 64)
    ns: dict = {}
    exec(compile(code, "<pair_consec>", "exec"), ns)
    fn = ns["pair_consec"]

    # Test 1: 4-vertex chain graph 0–1–2–3.
    G = [[0, 1, 0, 0],
         [1, 0, 1, 0],
         [0, 1, 0, 1],
         [0, 0, 1, 0]]
    M = [-1, -1, -1, -1]
    fn(G, 4, M)
    print(f"chain(4): M = {M}  (expect pairs (0,1) and (2,3))")
    assert M == [1, 0, 3, 2], f"got {M}"

    # Test 2: 6 vertices, edges (0-1), (2-3); (4,5) has no edge.
    G2 = [[0, 1, 0, 0, 0, 0],
          [1, 0, 0, 0, 0, 0],
          [0, 0, 0, 1, 0, 0],
          [0, 0, 1, 0, 0, 0],
          [0, 0, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 0]]
    M2 = [-1, -1, -1, -1, -1, -1]
    fn(G2, 6, M2)
    print(f"sparse(6): M = {M2}  (expect (0,1), (2,3), 4 and 5 unmatched)")
    assert M2 == [1, 0, 3, 2, -1, -1], f"got {M2}"

    # Test 3: n=0 (vacuous).
    M3: list[int] = []
    fn([], 0, M3)
    print(f"empty: M = {M3}")
    assert M3 == []

    # ── 4. Runtime-check mode validates every iteration ───────────
    print("=" * 64)
    print("Sample runs (runtime_check=True)")
    print("=" * 64)
    ns_rc: dict = {}
    exec(compile(code_rc, "<pair_consec_rc>", "exec"), ns_rc)
    fn_rc = ns_rc["pair_consec"]
    M_rc = [-1, -1, -1, -1]
    fn_rc(G, 4, M_rc)
    print(f"chain(4) under runtime_check: M = {M_rc}  (no ProofViolation)")
    assert M_rc == [1, 0, 3, 2]

    # Negative test: violate pre (M not initialized to all -1).
    from synth.proof_runtime import ProofViolation
    M_bad = [0, -1, -1, -1]   # M[0] = 0, violates pre.
    try:
        fn_rc(G, 4, M_bad)
        print("FAILED: expected ProofViolation on bad-pre input")
    except ProofViolation as e:
        print(f"OK: ProofViolation raised as expected ({e.kind})")

    # ── 5. emit_c: type signature, compile, run ───────────────────
    print()
    print("=" * 64)
    print("emit_c — int[][] -> int **")
    print("=" * 64)
    code_c = emit_c(sol, problem, fname="pair_consec")
    print(code_c)
    _compile_and_run_c(code_c)

    # ── 6. emit_rust: &[&[i64]], compile, run ─────────────────────
    print()
    print("=" * 64)
    print("emit_rust — int[][] -> &[&[i64]]")
    print("=" * 64)
    code_rs = emit_rust(sol, problem, fname="pair_consec")
    print(code_rs)
    _compile_and_run_rust(code_rs)

    print()
    print("Slice B.3 (1)-(4) — emit_py + emit_c + emit_rust — OK.")


def _compile_and_run_c(synth_c: str) -> None:
    """Wrap synth_c in a main() that calls pair_consec on a 4-vertex
    chain graph, compile with clang -Wall -Werror, run, assert
    stdout."""
    driver = r"""
#include <stdio.h>
int main(void) {
    int r0[] = {0, 1, 0, 0};
    int r1[] = {1, 0, 1, 0};
    int r2[] = {0, 1, 0, 1};
    int r3[] = {0, 0, 1, 0};
    int *G[] = {r0, r1, r2, r3};
    int M[] = {-1, -1, -1, -1};
    pair_consec(G, 4, M);
    printf("%d %d %d %d\n", M[0], M[1], M[2], M[3]);
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
        result = subprocess.run([out], check=True, capture_output=True,
                                text=True, timeout=10)
        out_str = result.stdout.strip()
    print(f"C binary stdout: {out_str!r}  (expect '1 0 3 2')")
    assert out_str == "1 0 3 2", f"got {out_str!r}"


def _compile_and_run_rust(synth_rs: str) -> None:
    """Wrap synth_rs in a main() that builds a 4-vertex chain graph
    as Vec<Vec<i64>>, threads it through a Vec<&[i64]> to match the
    `&[&[i64]]` signature, calls pair_consec, prints M."""
    driver = r"""
fn main() {
    let g: Vec<Vec<i64>> = vec![
        vec![0, 1, 0, 0],
        vec![1, 0, 1, 0],
        vec![0, 1, 0, 1],
        vec![0, 0, 1, 0],
    ];
    let g_refs: Vec<&[i64]> = g.iter().map(|v| v.as_slice()).collect();
    let mut m: Vec<i64> = vec![-1, -1, -1, -1];
    pair_consec(&g_refs, 4, &mut m);
    println!("{} {} {} {}", m[0], m[1], m[2], m[3]);
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
        result = subprocess.run([out], check=True, capture_output=True,
                                text=True, timeout=10)
        out_str = result.stdout.strip()
    print(f"Rust binary stdout: {out_str!r}  (expect '1 0 3 2')")
    assert out_str == "1 0 3 2", f"got {out_str!r}"


if __name__ == "__main__":
    main()
