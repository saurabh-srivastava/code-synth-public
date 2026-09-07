"""count_zeros — Phase X corpus benchmark (Lean-ish).

Count the number of zeros in the first n elements of an array.
Uses a UF with a **case-split** recurrence — Lean's `by_cases`
is the natural tactic; Z3's E-matching has to handle two
disjoint axiom forms.

Algorithm:
    c := 0; i := 0;
    while (i < n):
        if (A[i] == 0): c := c + 1; i := i + 1;
        else:           i := i + 1;

Spec:
    Pre  : n >= 0
    Post : c == count(A, n)

`count : (Int → Int) → Int → Int` is uninterpreted with the
case-split recurrence:
  - count(A, 0) = 0
  - A[k] == 0 ⇒ count(A, k+1) = count(A, k) + 1
  - A[k] ≠ 0 ⇒ count(A, k+1) = count(A, k)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n >= 0), "
        "return the number of zero entries among A[0], A[1], ..., "
        "A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("c", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("count", ["int[]", "int"], "int")],
    axioms = [
        "count(A, 0) == 0",
        ("ForAll(lambda k: Implies(k >= 0 and A[k] == 0, "
         "count(A, k + 1) == count(A, k) + 1))"),
        ("ForAll(lambda k: Implies(k >= 0 and A[k] != 0, "
         "count(A, k + 1) == count(A, k)))"),
    ],

    pre  = "n >= 0",
    post = "c == count(A, n)",

    atoms = {
        "s@B0": [{"c": "0", "i": "0"}],

        "tau@L0": [
            "c == count(A, i)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] == 0 → c := c + 1, i := i + 1
        "g@B1.0": ["A[i] == 0"],
        "s@B1.0": [{"c": "c + 1", "i": "i + 1"}],
        # Branch 1: A[i] != 0 → i := i + 1
        "g@B1.1": ["A[i] != 0"],
        "s@B1.1": [{"i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    # SOUND mode: hand-curated `.solved.lean` for per-branch sc#2
    # (A[i]==0) + sc#4 (A[i]!=0) + sc#7 (chain-bundle post).
    # The chain-bundle translator was extended for SB(n>1) loop
    # bodies (per-branch atoms, conjoined loop guard + branch
    # guard).  See lean/SynthLean/Y2Corpus/count_zeros/.
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/count_zeros",
    solver_timeout_ms = 900_000,
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
