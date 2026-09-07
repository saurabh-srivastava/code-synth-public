"""swap_first_last — Phase X corpus benchmark.

Exchange A[0] and A[n - 1] in place.  Pure acyclic — one nested
Update.  Different shape from `array_swap` (which takes arbitrary
indices).

Spec:
    Pre  : n >= 1 ∧ (∀k. 0 <= k < n ⇒ B[k] == A[k])
    Post : A[0] == B[n-1] ∧ A[n-1] == B[0] ∧
           (∀k. 0 < k < n-1 ⇒ A[k] == B[k])
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length at least n (with "
        "n >= 1), swap the first and last elements: A[0] and "
        "A[n-1] exchange values; all other elements unchanged."
    ),

    template = SB(n=1),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),   # ghost copy
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = ("(n >= 1) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = ("(A[0] == B[n - 1]) and (A[n - 1] == B[0]) and "
                "ForAll(lambda k: Implies("
                "0 < k and k < n - 1, A[k] == B[k]))"),
    atoms = {
        # Nested Update: swap A[0] and A[n-1].
        "s@B0": [
            {"A": "Update(Update(A, 0, A[n - 1]), n - 1, A[0])"},
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 60_000,
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
