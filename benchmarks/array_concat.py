"""array_concat — Phase X corpus benchmark.

Concatenate B onto A: produce array C such that the first n
elements are A[0..n) and the next m are B[0..m).  Single loop
over the second array, writing into C at offset n.

Spec:
    Pre  : n >= 0 ∧ m >= 0 ∧
           ForAll k. 0 <= k < n ⇒ C[k] == A[k]   (C starts with A's prefix)
    Post : ForAll k. 0 <= k < n ⇒ C[k] == A[k] ∧
           ForAll k. 0 <= k < m ⇒ C[n + k] == B[k]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n, an integer array B "
        "of length m, and an output array C pre-initialized so that "
        "C[k] == A[k] for 0 ≤ k < n, copy B[k] into C[n + k] for "
        "every k in 0..m-1.  Final C is the concatenation of A and B."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("C", "int[]", "input"),
                Var("n", "int", "input"),
                Var("m", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = ("(n >= 0) and (m >= 0) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, C[k] == A[k]))"),
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, C[k] == A[k])) and "
                "ForAll(lambda k: Implies(0 <= k and k < m, "
                "C[n + k] == B[k]))"),

    atoms = {
        "s@B0": [{"i": "0"}],
        "tau@L0": [
            "0 <= i",
            "i <= m",
            "n >= 0",
            "m >= 0",
            ("ForAll(lambda k: Implies(0 <= k and k < n, C[k] == A[k]))"),
            ("ForAll(lambda k: Implies(0 <= k and k < i, C[n + k] == B[k]))"),
        ],
        "g@L0":   ["i < m"],
        "phi@L0": ["m - i"],
        "s@B1": [{"C": "Update(C, n + i, B[i])", "i": "i + 1"}],
        "s@B2": [{}],
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
