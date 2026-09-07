"""clamp_array_range — Phase X corpus benchmark.

Clamp every element of A[0..n) to a [lo, hi] range, in place.
Loop body has SB(n=3) for the three input-range cases.

Spec:
    Pre  : n >= 0 ∧ lo <= hi ∧ B is a ghost copy of A
    Post : ForAll k. 0 <= k < n ⇒
             (B[k] < lo ∧ A[k] == lo) ∨
             (lo <= B[k] <= hi ∧ A[k] == B[k]) ∨
             (B[k] > hi ∧ A[k] == hi)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n (with n ≥ 0), and a "
        "range [lo, hi] (lo ≤ hi), clamp every element of A in place "
        "to the range: A[k] := lo if A[k] < lo, hi if A[k] > hi, "
        "otherwise A[k] unchanged."
    ),

    template = SB() >> Loop(SB(n=3)),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input"),
                Var("lo", "int", "input"),
                Var("hi", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = ("(n >= 0) and (lo <= hi) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = (
        "ForAll(lambda k: Implies("
        "0 <= k and k < n, "
        "((B[k] < lo) and (A[k] == lo)) or "
        "((lo <= B[k]) and (B[k] <= hi) and (A[k] == B[k])) or "
        "((B[k] > hi) and (A[k] == hi))))"
    ),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            "lo <= hi",
            # Already-clamped prefix.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, "
             "((B[k] < lo) and (A[k] == lo)) or "
             "((lo <= B[k]) and (B[k] <= hi) and (A[k] == B[k])) or "
             "((B[k] > hi) and (A[k] == hi))))"),
            # Tail unchanged from B.
            ("ForAll(lambda k: Implies("
             "i <= k and k < n, A[k] == B[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "g@B1.0": ["A[i] < lo"],
        "s@B1.0": [{"A": "Update(A, i, lo)", "i": "i + 1"}],
        "g@B1.1": ["A[i] > hi"],
        "s@B1.1": [{"A": "Update(A, i, hi)", "i": "i + 1"}],
        "g@B1.2": ["(lo <= A[i]) and (A[i] <= hi)"],
        "s@B1.2": [{"i": "i + 1"}],
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
