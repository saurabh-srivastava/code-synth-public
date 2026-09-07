"""all_positive — Phase X corpus benchmark.

Check whether ALL elements of A[0..n) are positive.  Returns
1 if so, 0 otherwise.  Single-pass loop with early-set flag,
branched body.

Spec:
    Pre  : n >= 0
    Post : (result == 1 ∧ ∀k. 0 ≤ k < n ⇒ A[k] > 0)
         ∨ (result == 0 ∧ ∃k. 0 ≤ k < n ∧ A[k] <= 0)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "return 1 if every element A[0], A[1], ..., A[n-1] is "
        "strictly positive, otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n >= 0",
    # result is 1 iff all elements are positive.
    post     = (
        "((result == 1) and "
        " ForAll(lambda k: Implies(0 <= k and k < n, A[k] > 0))) or "
        "((result == 0) and "
        " Exists(lambda k: 0 <= k and k < n and A[k] <= 0))"
    ),

    atoms = {
        # Init: flag := 1, i := 0.
        "s@B0": [{"flag": "1", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # flag is 1 iff prefix [0, i) is all-positive.
            ("((flag == 1) and "
             " ForAll(lambda k: Implies(0 <= k and k < i, A[k] > 0))) or "
             "((flag == 0) and "
             " Exists(lambda k: 0 <= k and k < i and A[k] <= 0))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] > 0 → flag stays, advance i.
        "g@B1.0": ["A[i] > 0"],
        "s@B1.0": [{"i": "i + 1"}],
        # Branch 1: A[i] <= 0 → flag := 0, advance i.
        "g@B1.1": ["A[i] <= 0"],
        "s@B1.1": [{"flag": "0", "i": "i + 1"}],

        # Final: result := flag.
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
