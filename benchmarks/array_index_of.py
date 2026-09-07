"""array_index_of — Phase X corpus benchmark.

Find the index of the first occurrence of `t` in A[0..n), or
return n if absent.  Like find_first_pos but with a parameter
target instead of "is positive".

Spec:
    Pre  : n >= 0
    Post : (idx == n ∧ ForAll k. 0 ≤ k < n ⇒ A[k] != t)
         ∨ (0 <= idx < n ∧ A[idx] == t ∧
            ForAll k. 0 ≤ k < idx ⇒ A[k] != t)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n (with n ≥ 0), and a "
        "target value t, return the index of the first occurrence "
        "of t in A[0..n).  If t doesn't appear, return n."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("t", "int", "input")],
    outputs  = [Var("idx", "int", "output")],

    pre      = "n >= 0",
    post     = (
        "((idx == n) and "
        " ForAll(lambda k: Implies(0 <= k and k < n, A[k] != t))) or "
        "((0 <= idx) and (idx < n) and (A[idx] == t) and "
        " ForAll(lambda k: Implies(0 <= k and k < idx, A[k] != t)))"
    ),

    atoms = {
        "s@B0": [{"idx": "0"}],
        "tau@L0": [
            "0 <= idx",
            "idx <= n",
            "n >= 0",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < idx, A[k] != t))"),
        ],
        # Continue while still scanning AND haven't found t yet.
        "g@L0":   ["(idx < n) and (A[idx] != t)"],
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
