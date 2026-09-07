"""abs_array — Phase X corpus benchmark.

In-place absolute value: A[i] := |A[i]| for 0 ≤ i < n.  Loop
body has a 2-way branch on the sign of A[i].  Quantified prefix
invariant.

Spec:
    Pre  : n >= 0 ∧ B is a ghost copy of input A
    Post : ForAll k. 0 ≤ k < n ⇒ A[k] == |B[k]|

The ghost copy `B` lets the spec reference the original
(pre-loop) values; the loop overwrites A in place.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "replace each entry A[k] with its absolute value, |A[k]|, "
        "for 0 ≤ k < n."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = ("(n >= 0) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = ("ForAll(lambda k: Implies("
                "0 <= k and k < n, "
                "((B[k] >= 0 and A[k] == B[k]) or "
                " (B[k] < 0 and A[k] == 0 - B[k]))))"),

    atoms = {
        "s@B0": [{"i": "0"}],
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # Carry the ghost-copy correspondence outside the
            # rewritten prefix.
            ("ForAll(lambda k: Implies("
             "i <= k and k < n, A[k] == B[k]))"),
            # Rewritten prefix satisfies |B[k]|.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, "
             "((B[k] >= 0 and A[k] == B[k]) or "
             " (B[k] < 0 and A[k] == 0 - B[k]))))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] ≥ 0 → no change, just i := i + 1.
        "g@B1.0": ["A[i] >= 0"],
        "s@B1.0": [{"i": "i + 1"}],
        # Branch 1: A[i] < 0 → A[i] := -A[i]; i := i + 1.
        "g@B1.1": ["A[i] < 0"],
        "s@B1.1": [{"A": "Update(A, i, 0 - A[i])", "i": "i + 1"}],
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
