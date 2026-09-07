"""clamp_array_positive — Phase X corpus benchmark.

Element-wise clamp to non-negative: B[k] = max(0, A[k]).  Per-
element conditional — the loop body is an SB(n=2) (if A[k] < 0,
write 0, else copy A[k]).  Tests conditional inside Loop with
both branches modifying the same output array.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  B[k] == max(0, A[k])

Encoded by case-split: (A[k] < 0 → B[k] == 0) ∧
                        (A[k] >= 0 → B[k] == A[k]).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, an integer array B, and a length "
        "n (with n >= 0), populate B so that B[k] equals max(0, A[k]) "
        "for every k in [0, n) — i.e., copy A[k] when it's non-"
        "negative, otherwise write 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda k: Implies(0 <= k and k < n, "
                "((A[k] < 0 and B[k] == 0) or "
                " (A[k] >= 0 and B[k] == A[k]))))"),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "((A[k] < 0 and B[k] == 0) or "
             " (A[k] >= 0 and B[k] == A[k]))))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Loop body: SB(n=2)
        # Branch 0: A[i] < 0 → B[i] := 0
        "g@B1.0": ["A[i] < 0", "A[i] <= 0"],
        "s@B1.0": [{"B": "Update(B, i, 0)", "i": "i + 1"}],
        # Branch 1: A[i] >= 0 → B[i] := A[i]
        "g@B1.1": ["A[i] >= 0", "A[i] > 0"],
        "s@B1.1": [{"B": "Update(B, i, A[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 2,
    expected_solutions = 2,
    expected_lean_hits = 0,
    solver_timeout_ms = 120_000,
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
