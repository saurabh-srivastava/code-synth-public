"""is_sorted — Phase X corpus benchmark.

Check whether A[0..n) is non-decreasing.  Returns 1 if sorted,
0 if not.  Uses an early-exit loop guard and a flag.

Spec:
    Pre  : n >= 0
    Post : (result == 1 ∧ ∀k. 0 ≤ k < n-1 ⇒ A[k] <= A[k+1])
         ∨ (result == 0 ∧ ∃k. 0 ≤ k < n-1 ∧ A[k] > A[k+1])
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "return 1 if A[0] ≤ A[1] ≤ ... ≤ A[n-1] (non-decreasing), "
        "otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n >= 0",
    post     = (
        "((result == 1) and "
        " ForAll(lambda k: Implies("
        "0 <= k and k < n - 1, A[k] <= A[k + 1]))) or "
        "((result == 0) and "
        " Exists(lambda k: 0 <= k and k < n - 1 and A[k] > A[k + 1]))"
    ),

    atoms = {
        "s@B0": [{"flag": "1", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            ("((flag == 1) and "
             " ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] <= A[k + 1] or k == n - 1))) or "
             "((flag == 0) and "
             " Exists(lambda k: 0 <= k and k < n - 1 and A[k] > A[k + 1]))"),
        ],
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] <= A[i+1] → no flip; advance.
        "g@B1.0": ["A[i] <= A[i + 1]"],
        "s@B1.0": [{"i": "i + 1"}],
        # Branch 1: A[i] > A[i+1] → flag := 0; advance.
        "g@B1.1": ["A[i] > A[i + 1]"],
        "s@B1.1": [{"flag": "0", "i": "i + 1"}],

        "s@B2": [{"result": "flag"}],
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
