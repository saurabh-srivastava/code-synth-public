"""array_zero — Phase 3.C smoke test for array writes (z3 Store).

Zero out the first n elements of an array via a single loop:

    i := 0;
    while (i < n) {
        A := Update(A, i, 0);
        i := i + 1;
    }

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  A[k] == 0

Invariant: ForAll k. 0 <= k < i ⇒ A[k] == 0;  also 0 <= i <= n.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",
    atoms = {
        # Conjunctive τ.
        "tau@L0": [
            "ForAll(lambda k: Implies(0 <= k and k < i, A[k] == 0))",  # the key
            "0 <= i",
            "i <= n",
            "i >= 1",                           # too strong for entry (i starts at 0)
        ],
        "g@L0":  ["i < n", "i <= n"],
        "phi@L0": ["n - i", "n"],
        # Entry: i := 0; A unchanged.
        "s@B0": [
            {"i": "0"},                                 # published
            {"i": "1"},
            {"i": "n"},
        ],
        # Body: A := Update(A, i, 0); i := i + 1.
        # This is a SEQUENTIAL (SSA) atom — second assignment uses
        # the i preserved by the first.  Actually since A and i are
        # both being assigned, and only i appears on the RHS of A's
        # update, we can express it as a parallel-assign dict:
        "s@B1": [
            {"A": "Update(A, i, 0)", "i": "i + 1"},     # published
            {"A": "Update(A, i, 1)", "i": "i + 1"},
            {"i": "i + 1"},                              # doesn't zero anything
        ],
        # Exit: identity
        "s@B2": [ {} ],
    },
    max_solutions = 3,
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
