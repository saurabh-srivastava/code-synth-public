"""min_index — Phase X corpus benchmark.

Argmin: return the index of the smallest element.  Differs from
`min_array` in that the output is the INDEX, not the value —
useful corpus variety: many real tasks return a position rather
than a magnitude.

Spec:
    Pre  : n >= 1
    Post : 0 <= idx < n ∧ ForAll k. 0 <= k < n ⇒ A[idx] <= A[k]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n >= 1), "
        "return the index of the smallest element of A[0..n-1].  "
        "If multiple positions tie for the minimum, return the "
        "first one."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("idx", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 1",
    post     = ("(0 <= idx) and (idx < n) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, "
                "A[idx] <= A[k]))"),

    atoms = {
        # idx, i := 0, 1
        "s@B0": [
            {"idx": "0", "i": "1"},
            {"idx": "0", "i": "0"},
        ],

        "tau@L0": [
            "0 <= idx",
            "idx < i",
            "i <= n",
            "i >= 1",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "A[idx] <= A[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0 (A[i] < A[idx]): idx := i, i := i + 1
        "g@B1.0": ["A[i] < A[idx]", "A[i] <= A[idx]"],
        "s@B1.0": [{"idx": "i", "i": "i + 1"}],
        # Branch 1 (else): i := i + 1
        "g@B1.1": ["A[i] >= A[idx]", "A[i] > A[idx]"],
        "s@B1.1": [{"i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 4,
    expected_solutions = 4,
    expected_lean_hits = 0,
    solver_timeout_ms = 180_000,
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
