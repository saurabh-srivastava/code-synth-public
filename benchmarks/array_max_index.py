"""array_max_index — Phase X corpus benchmark.

Find the index of the (first) maximum element in A[0..n).
Like `min_index.py` but for the max.

Spec:
    Pre  : n >= 1
    Post : 0 <= idx < n
         ∧ ForAll k. 0 <= k < n ⇒ A[k] <= A[idx]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 1), "
        "return the index of the maximum element among "
        "A[0], A[1], ..., A[n-1] (the first occurrence on ties)."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("idx", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "n >= 1",
    post     = (
        "(0 <= idx) and (idx < n) and "
        "ForAll(lambda k: Implies("
        "0 <= k and k < n, A[k] <= A[idx]))"
    ),

    atoms = {
        # Init: idx := 0, i := 1.
        "s@B0": [{"idx": "0", "i": "1"}],

        "tau@L0": [
            "0 <= idx",
            "idx < n",
            "1 <= i",
            "i <= n",
            "n >= 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] <= A[idx]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] > A[idx] → idx := i.
        "g@B1.0": ["A[i] > A[idx]"],
        "s@B1.0": [{"idx": "i", "i": "i + 1"}],
        # Branch 1: A[i] <= A[idx] → no idx change.
        "g@B1.1": ["A[i] <= A[idx]"],
        "s@B1.1": [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
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
