"""find_first_pos — Phase X corpus benchmark.

Find the index of the first positive element in A[0..n), or n
if none exists.  Uses an early-exit guard `idx < n ∧ A[idx] <= 0`
on the loop: the loop terminates either when idx hits n (no
positive found) OR when A[idx] > 0 (first positive found).

Spec:
    Pre  : n >= 0
    Post : (idx == n ∧ ForAll k. 0 ≤ k < n ⇒ A[k] <= 0)
         ∨ (0 <= idx < n ∧ A[idx] > 0 ∧
            ForAll k. 0 ≤ k < idx ⇒ A[k] <= 0)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n >= 0), "
        "return the index of the first strictly-positive element "
        "in A[0..n).  If no element is positive, return n."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("idx", "int", "output")],

    pre      = "n >= 0",
    post     = (
        "((idx == n) and "
        " ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= 0))) or "
        "((0 <= idx) and (idx < n) and (A[idx] > 0) and "
        " ForAll(lambda k: Implies(0 <= k and k < idx, A[k] <= 0)))"
    ),

    atoms = {
        "s@B0": [{"idx": "0"}],
        "tau@L0": [
            "0 <= idx",
            "idx <= n",
            "n >= 0",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < idx, A[k] <= 0))"),
        ],
        # Early-exit loop: continue iff still scanning AND haven't
        # hit a positive yet.  Loop body advances idx.
        "g@L0":   ["(idx < n) and (A[idx] <= 0)"],
        "phi@L0": ["n - idx"],
        "s@B1": [{"idx": "idx + 1"}],
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
