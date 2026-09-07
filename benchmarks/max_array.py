"""max_array — Phase 3.A/3.B benchmark.

Synthesize the body of `m = max(A[0..n-1])` for `n >= 1`:

    m, i := A[0], 1;
    while (i < n) {
        if (A[i] > m) { m, i := A[i], i + 1; }
        else          { i := i + 1; }
    }

Exercises:
  • Phase 3.A — array typed variables, `A[k]` read syntax (z3 Select).
  • Phase 3.B — quantified invariant atoms via `ForAll(lambda k: …)`.
  • Phase 2.5 — `SB(n=2)` for the if/else inside the loop body.
  • Phase 2   — conjunctive τ.

Spec:
    Pre  : n >= 1
    Post : ForAll k. 0 <= k < n ⇒ A[k] <= m
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 1",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= m))",
    atoms = {
        # Conjunctive τ — atomic predicates including a quantified one.
        "tau@L0": [
            "ForAll(lambda k: Implies(0 <= k and k < i, A[k] <= m))",  # the key invariant
            "i >= 1",                                                   # often needed
            "i <= n",                                                   # often needed
            "0 <= i",                                                   # weaker than `i >= 1`
            "m == A[0]",                                                # distractor (only initially)
        ],
        # Loop guard.
        "g@L0":  ["i < n", "i <= n", "i > 0"],
        # Ranking.
        "phi@L0": ["n - i", "n", "i"],

        # Entry: m, i := A[0], 1
        "s@B0": [
            {"m": "A[0]", "i": "1"},                                    # published
            {"m": "0",    "i": "0"},
            {"m": "A[0]", "i": "0"},
        ],

        # Loop body: SB(n=2)
        # Branch 0 (A[i] > m): m, i := A[i], i + 1
        "g@B1.0": ["A[i] > m", "A[i] >= m", "A[i] < m"],
        "s@B1.0": [
            {"m": "A[i]", "i": "i + 1"},                                # published
            {"i": "i + 1"},
            {"m": "A[i]"},
        ],
        # Phase 3.I: branch 1's explicit guard.
        "g@B1.1": [
            "A[i] <= m",                                                # published — the "else"
            "A[i] < m",
            "A[i] > m",
        ],
        # Branch 1 (else): i := i + 1
        "s@B1.1": [
            {"i": "i + 1"},                                             # published
            {"m": "A[i]", "i": "i + 1"},
            {},                                                          # skip — wrong (infinite loop)
        ],

        # Exit: identity
        "s@B2": [ {} ],
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
