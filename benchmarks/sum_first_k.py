"""sum_first_k — Phase X corpus benchmark.

Like `sum_array` but with a parametric prefix length `k`
(0 ≤ k ≤ n), returning `Σ A[0..k)`.  Uses the same `sum` UF as
sum_array, demonstrating that an existing axiom set composes
with a different program shape.

Spec:
    Pre  : 0 <= k <= n
    Post : s == sum(A, k)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n, and a target prefix "
        "length k (with 0 ≤ k ≤ n), return the sum of A[0], A[1], "
        "..., A[k-1]."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("k", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("sum", ["int[]", "int"], "int")],
    axioms = [
        "sum(A, 0) == 0",
        ("ForAll(lambda j: Implies(j >= 0, "
         "sum(A, j + 1) == sum(A, j) + A[j]))"),
    ],

    pre  = "(0 <= k) and (k <= n)",
    post = "s == sum(A, k)",

    atoms = {
        "s@B0": [{"s": "0", "i": "0"}],
        "tau@L0": [
            "s == sum(A, i)",
            "0 <= i",
            "i <= k",
            "k <= n",
        ],
        "g@L0":   ["i < k"],
        "phi@L0": ["k - i"],
        "s@B1": [{"s": "s + A[i]", "i": "i + 1"}],
        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/sum_first_k",
    solver_timeout_ms = 1_800_000,   # 30 min budget for axiom-heavy
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    print(f"wall: {time.monotonic() - t:.1f}s")
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
