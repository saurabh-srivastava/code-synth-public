"""array_shift_right — Phase X corpus benchmark.

Shift the first n-1 elements of A right by 1, dropping A[n-1]
and inserting `v` at A[0].  Loop iterates from the right
inward, copying A[i-1] into A[i].

Spec:
    Pre  : n >= 1 ∧ B is a ghost copy of A
    Post : A[0] == v
         ∧ ForAll k. 1 ≤ k < n ⇒ A[k] == B[k - 1]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length at least n (with n ≥ 1) "
        "and a value v, shift A's first n-1 elements one position "
        "to the right (dropping A[n-1]) and insert v at A[0]."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input"),
                Var("v", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = ("(n >= 1) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = (
        "(A[0] == v) and "
        "ForAll(lambda k: Implies("
        "1 <= k and k < n, A[k] == B[k - 1]))"
    ),

    atoms = {
        # Init: i := n - 1 (the rightmost write target).
        "s@B0": [{"i": "n - 1"}],

        "tau@L0": [
            "0 <= i",
            "i <= n - 1",
            "n >= 1",
            # Positions strictly right of i are already shifted.
            ("ForAll(lambda k: Implies("
             "i < k and k < n, A[k] == B[k - 1]))"),
            # Positions at and left of i still hold the original A.
            ("ForAll(lambda k: Implies("
             "0 <= k and k <= i, A[k] == B[k]))"),
        ],
        "g@L0":   ["i > 0"],
        "phi@L0": ["i"],

        # Body: A[i] := A[i - 1], i := i - 1.
        "s@B1": [{"A": "Update(A, i, A[i - 1])", "i": "i - 1"}],

        # Final: A[0] := v.
        "s@B2": [{"A": "Update(A, 0, v)"}],
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
