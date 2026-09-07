"""min_array — Phase X corpus benchmark.

Parallel to max_array but with the inverted comparison.  Tests
that the synthesizer doesn't depend on the > vs < direction of
the comparison in the inductive invariant — a useful symmetry
check.

Spec:
    Pre  : n >= 1
    Post : ForAll k. 0 <= k < n  ⇒  m <= A[k]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    # English description — Phase X corpus pair input (driver-LLM
    # ICL).  Phrased as a user would; NOT implementer notes.
    description = (
        "Given an integer array A and a length n (with n >= 1), "
        "return the minimum value among the elements A[0], A[1], "
        "..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 1",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, m <= A[k]))",

    atoms = {
        # Conjunctive τ — atomic predicates including a quantified one.
        "tau@L0": [
            "ForAll(lambda k: Implies(0 <= k and k < i, m <= A[k]))",   # key
            "i >= 1",
            "i <= n",
            "0 <= i",                                                    # weaker
            "m == A[0]",                                                 # initial-only distractor
        ],
        "g@L0":   ["i < n", "i <= n", "i > 0"],
        "phi@L0": ["n - i", "n", "i"],

        # Entry: m, i := A[0], 1
        "s@B0": [
            {"m": "A[0]", "i": "1"},                                     # published
            {"m": "0",    "i": "0"},
            {"m": "A[0]", "i": "0"},
        ],

        # Loop body: SB(n=2)
        # Branch 0 (A[i] < m): m, i := A[i], i + 1
        "g@B1.0": ["A[i] < m", "A[i] <= m", "A[i] > m"],
        "s@B1.0": [
            {"m": "A[i]", "i": "i + 1"},                                 # published
            {"i": "i + 1"},
            {"m": "A[i]"},
        ],
        "g@B1.1": ["A[i] >= m", "A[i] > m", "A[i] < m"],
        "s@B1.1": [
            {"i": "i + 1"},                                              # published
            {"m": "A[i]", "i": "i + 1"},
            {},
        ],

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
