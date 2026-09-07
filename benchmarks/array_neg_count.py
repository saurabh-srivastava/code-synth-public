"""array_neg_count — Phase X corpus benchmark.

Count negative elements in A[0..n).  Same shape as count_zeros /
count_equal — UF + case-split recurrence — but the predicate is
`A[k] < 0` instead of `A[k] == 0` or `A[k] == t`.

Spec:
    Pre  : n >= 0
    Post : c == count_neg(A, n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "return the number of strictly-negative elements among "
        "A[0], A[1], ..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("c", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("count_neg", ["int[]", "int"], "int")],
    axioms = [
        "count_neg(A, 0) == 0",
        ("ForAll(lambda k: Implies(k >= 0 and A[k] < 0, "
         "count_neg(A, k + 1) == count_neg(A, k) + 1))"),
        ("ForAll(lambda k: Implies(k >= 0 and A[k] >= 0, "
         "count_neg(A, k + 1) == count_neg(A, k)))"),
    ],

    pre  = "n >= 0",
    post = "c == count_neg(A, n)",

    atoms = {
        "s@B0": [{"c": "0", "i": "0"}],

        "tau@L0": [
            "c == count_neg(A, i)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "g@B1.0": ["A[i] < 0"],
        "s@B1.0": [{"c": "c + 1", "i": "i + 1"}],
        "g@B1.1": ["A[i] >= 0"],
        "s@B1.1": [{"i": "i + 1"}],

        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/array_neg_count",
    solver_timeout_ms = 1_800_000,
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
