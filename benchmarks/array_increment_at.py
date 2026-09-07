"""array_increment_at — Phase X corpus benchmark.

Increment a single element at index `k` by 1: A[k] := A[k] + 1.
Acyclic — one transition with an Update.  Other elements
unchanged.

Spec:
    Pre  : (0 <= k < n) ∧ (∀p. 0 ≤ p < n ⇒ B[p] == A[p])
    Post : A[k] == B[k] + 1 ∧ (∀p. 0 ≤ p < n ∧ p != k ⇒ A[p] == B[p])
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and an index k (with 0 ≤ k < n), "
        "increment A[k] by 1.  All other elements unchanged."
    ),

    template = SB(n=1),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("k", "int", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = ("(0 <= k) and (k < n) and "
                "ForAll(lambda p: Implies(0 <= p and p < n, B[p] == A[p]))"),
    post     = ("(A[k] == B[k] + 1) and "
                "ForAll(lambda p: Implies("
                "0 <= p and p < n and p != k, A[p] == B[p]))"),
    atoms = {
        "s@B0": [{"A": "Update(A, k, A[k] + 1)"}],
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
