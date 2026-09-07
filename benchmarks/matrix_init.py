"""matrix_init — Phase 3.S: 2D matrix zero-fill.

Stepping stone to LCS / DP benchmarks.  Validates native `int[][]`
support (added in Phase 3.S framework extension) by zero-filling
an m × n matrix.  Indices are NATIVE 2D — `A[i][j]` parses to
`Select(Select(A, i), j)`, `Update(A, i, j, 0)` to a nested
`Store`.  This sidesteps the quantified-nonlinear-arithmetic wall
that the 1D-flattened version hit (Z3 couldn't reason about
`p*n+q == i*n+j` under universal quantifiers).

    i := 0
    while (i < m):
        j := 0
        while (j < n):
            A[i][j] := 0
            j := j + 1
        i := i + 1
    // post: ∀p, q. 0 ≤ p < m ∧ 0 ≤ q < n  ⇒  A[p][q] == 0

Spec:
    Pre  : m ≥ 0 ∧ n ≥ 0
    Post : ForAll(p, q: 0 ≤ p < m ∧ 0 ≤ q < n  ⇒  A[p][q] == 0)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1) >> Loop(SB(n=1)) >> SB(n=1)),
    inputs   = [Var("m", "int", "input"),
                Var("n", "int", "input"),
                Var("A", "int[][]", "input")],
    outputs  = [Var("A", "int[][]", "output")],
    locals   = [Var("i", "int", "local"), Var("j", "int", "local")],
    pre      = "m >= 0 and n >= 0",
    post     = ("ForAll(lambda p, q: Implies("
                "0 <= p and p < m and 0 <= q and q < n, "
                "A[p][q] == 0))"),

    atoms = {
        # SB0: i := 0.
        "s@B0": [{"i": "0"}],

        # Outer τ: rows < i are fully zeroed.
        "tau@L0": [
            "0 <= i",
            "i <= m",
            "m >= 0",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p < i and 0 <= q and q < n, "
             "A[p][q] == 0))"),
        ],
        "g@L0":   ["i < m"],
        "phi@L0": ["m - i"],

        # SB1: j := 0.
        "s@B1": [{"j": "0"}],

        # Inner τ.
        "tau@L1": [
            "0 <= j",
            "j <= n",
            "i < m",
            "m >= 0", "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p < i and 0 <= q and q < n, "
             "A[p][q] == 0))"),
            ("ForAll(lambda q: Implies("
             "0 <= q and q < j, A[i][q] == 0))"),
        ],
        "g@L1":   ["j < n"],
        "phi@L1": ["n - j"],

        # Inner body: A[i][j] := 0; j := j+1.
        "s@B2": [{"A": "Update(A, i, j, 0)", "j": "j + 1"}],

        # SB3: i := i + 1.
        "s@B3": [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,   # 10 min
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    elapsed = time.monotonic() - t
    print(f"wall: {elapsed:.1f}s")
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
