"""count_equal — Phase X corpus benchmark.

Count occurrences of a target value `t` in A[0..n).  Uses an
uninterpreted-function `count_eq` parameterized by the target,
case-split recurrence (similar to count_zeros but with a
runtime-parameter target).

Spec:
    Pre  : n >= 0
    Post : c == count_eq(A, n, t)

`count_eq : (Int → Int) → Int → Int → Int` axiomatized with:
  - count_eq(A, 0, t) = 0
  - A[k] == t ⇒ count_eq(A, k+1, t) = count_eq(A, k, t) + 1
  - A[k] != t ⇒ count_eq(A, k+1, t) = count_eq(A, k, t)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n (with n ≥ 0), and "
        "a target value t, count the number of elements among "
        "A[0], A[1], ..., A[n-1] that equal t."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("t", "int", "input")],
    outputs  = [Var("c", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("count_eq", ["int[]", "int", "int"], "int")],
    axioms = [
        "count_eq(A, 0, t) == 0",
        ("ForAll(lambda k: Implies(k >= 0 and A[k] == t, "
         "count_eq(A, k + 1, t) == count_eq(A, k, t) + 1))"),
        ("ForAll(lambda k: Implies(k >= 0 and A[k] != t, "
         "count_eq(A, k + 1, t) == count_eq(A, k, t)))"),
    ],

    pre  = "n >= 0",
    post = "c == count_eq(A, n, t)",

    atoms = {
        "s@B0": [{"c": "0", "i": "0"}],

        "tau@L0": [
            "c == count_eq(A, i, t)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] == t → c := c + 1, i := i + 1.
        "g@B1.0": ["A[i] == t"],
        "s@B1.0": [{"c": "c + 1", "i": "i + 1"}],
        # Branch 1: A[i] != t → i := i + 1.
        "g@B1.1": ["A[i] != t"],
        "s@B1.1": [{"i": "i + 1"}],

        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/count_equal",
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
