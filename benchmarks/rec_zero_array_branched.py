"""rec_zero_array_branched — Phase 3.I validation: SB(n>1) in a chain.

Recursive zero-out where the post-processing step is *conditional*:

    A := f(A, n - 1);
    if (n > 0) { A[n - 1] := 0; }
    else       { /* skip */ }

Template: `Recur >> SB(n=2)`.  This is the SB(n>1)-in-chain shape
that Phase 3.I unlocks — the bundle enumerates Cartesian paths over
the SB's branches (one path per branch combination) and emits a
coverage constraint at the SB.

Notice the trivial `else` skip branch is correct (because n=0 hits
the vacuously-true Post).  Coverage `⋁ g_i ≡ true` ensures one of
the two guards holds for every reachable n.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  A[k] == 0
"""
from synth import Problem, SB, Recur, Var, solve


PROBLEM = Problem(
    template = Recur() >> SB(n=2),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",

    atoms = {
        # Recur transition.
        "s@R0": [
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},
             "ret":  {"A": "A"}},
            {"_recur": True,
             "args": {"A": "A", "n": "n"},                    # no decrease
             "ret":  {"A": "A"}},
        ],
        # SB(n=2): conditional post-processing.
        # Branch 0: "n > 0" → update A[n-1] := 0.
        "g@B0.0": [
            "n > 0",                                          # published
            "n >= 1",
            "n >= 0",                                          # too inclusive — would also fire for n=0
        ],
        "s@B0.0": [
            {"A": "Update(A, n - 1, 0)"},                     # published
            {"A": "Update(A, n, 0)"},                          # wrong index
        ],
        # Branch 1: "n <= 0" → skip.
        "g@B0.1": [
            "n <= 0",                                         # published — the "else"
            "n == 0",
            "n < 0",                                           # doesn't cover n=0
        ],
        "s@B0.1": [
            {},                                                # published — skip (no-op)
            {"A": "Update(A, n - 1, 0)"},                      # wrong for the else branch
        ],
        "phi@PROC": ["n", "0"],
    },
    max_solutions = 5,
    expected_solutions = 5,
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
