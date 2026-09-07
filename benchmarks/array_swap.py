"""array_swap — Phase X corpus benchmark.

Swap two array positions in place: given indices i, j, exchange
A[i] and A[j].  Pure acyclic — no loop, just a parallel swap on
the array.  Tests Update-of-Update patterns the synthesizer
already handles in bubble_sort but in a much simpler context.

Spec:
    Pre  : 0 <= i < n ∧ 0 <= j < n
    Post : A[i] == old_A[j] ∧ A[j] == old_A[i] ∧
           ForAll k. (k != i ∧ k != j) ⇒ A[k] == old_A[k]

The "old_A" trick: we pass A both as input and (logically) as a
ghost reference.  Since SMT doesn't carry an `old`, we use
parameter `B` to represent the original — Pre says B == A, Post
constrains both.
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, indices i and j (both valid for "
        "A), exchange the values at positions i and j in A.  All "
        "other positions are unchanged."
    ),

    template = SB(n=1),
    # B is the ghost copy of the original A (caller passes A twice).
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("i", "int", "input"),
                Var("j", "int", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = ("(0 <= i) and (i < n) and (0 <= j) and (j < n) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = ("(A[i] == B[j]) and (A[j] == B[i]) and "
                "ForAll(lambda k: Implies("
                "0 <= k and k < n and k != i and k != j, A[k] == B[k]))"),

    atoms = {
        # Single transition: swap via nested Update (bubble-sort style).
        "s@B0": [
            {"A": "Update(Update(A, i, A[j]), j, A[i])"},
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
