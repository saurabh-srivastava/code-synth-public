"""grid_paths — Phase 3.S: count monotone paths in a grid (2D DP).

**Known timeout** (>10 min, 2026-05-14).  Documented research
data point, **not in the regression suite**.

Stepping stone between matrix_init (works, 6s) and lcs (timeout).
Adds an uninterpreted function + recurrence axiom on top of the
2D DP shape, but with NO case split — single equation `f(i, j) =
f(i-1, j) + f(i, j-1)`.  Establishes that the LCS wedge is NOT
caused by the case-split: even a single-equation 2D recurrence
+ UF axiom + 2D-array invariant exceeds Z3's quantifier-
instantiation budget at our current encoding.  The bottleneck is
each per-class Z3 check (~5s+) times 2^|τ_inner| subsets times
multiple constraints — axiom-heavy 2D DPs are at the edge of
feasibility.

    i := 1
    while (i <= m):
        j := 1
        while (j <= n):
            L[i][j] := L[i-1][j] + L[i][j-1]
            j := j + 1
        i := i + 1
    result := L[m][n]
    // post: result == paths(m, n)

`paths(i, j)` = number of monotone lattice paths from (0, 0) to
(i, j) moving only right/down.  Recurrence supplied as axioms.
Base case: paths(0, j) = 1, paths(i, 0) = 1.

Spec:
    Pre  : m ≥ 0 ∧ n ≥ 0 ∧ L pre-initialized: L[p][0] = 1, L[0][q] = 1
    Post : result == paths(m, n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = (
        SB(n=1)
        >> Loop(SB(n=1) >> Loop(SB(n=1)) >> SB(n=1))
        >> SB(n=1)
    ),
    inputs = [
        Var("m", "int", "input"),
        Var("n", "int", "input"),
        Var("L", "int[][]", "input"),
    ],
    outputs = [
        Var("L", "int[][]", "output"),
        Var("result", "int", "output"),
    ],
    locals = [
        Var("i", "int", "local"),
        Var("j", "int", "local"),
    ],

    uninterpreted = [("paths", ["int", "int"], "int")],
    axioms = [
        # Base cases.
        "ForAll(lambda j: Implies(j >= 0, paths(0, j) == 1))",
        "ForAll(lambda i: Implies(i >= 0, paths(i, 0) == 1))",
        # Recurrence.
        ("ForAll(lambda i, j: Implies("
         "i >= 1 and j >= 1, "
         "paths(i, j) == paths(i-1, j) + paths(i, j-1)))"),
    ],

    # Pre: L initialized with row 0 and col 0 to 1.
    pre = ("m >= 0 and n >= 0 and "
           "ForAll(lambda q: Implies(0 <= q and q <= n, L[0][q] == 1)) and "
           "ForAll(lambda p: Implies(0 <= p and p <= m, L[p][0] == 1))"),
    post = "result == paths(m, n)",

    atoms = {
        "s@B0": [{"i": "1"}],

        "tau@L0": [
            "1 <= i",
            "i <= m + 1",
            "m >= 0",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p < i and 0 <= q and q <= n, "
             "L[p][q] == paths(p, q)))"),
            ("ForAll(lambda p: Implies("
             "0 <= p and p <= m, L[p][0] == 1))"),
        ],
        "g@L0":   ["i <= m"],
        "phi@L0": ["m - i + 1"],

        "s@B1": [{"j": "1"}],

        "tau@L1": [
            "1 <= i", "i <= m",
            "1 <= j", "j <= n + 1",
            "m >= 0", "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p < i and 0 <= q and q <= n, "
             "L[p][q] == paths(p, q)))"),
            ("ForAll(lambda q: Implies("
             "0 <= q and q < j, "
             "L[i][q] == paths(i, q)))"),
            ("ForAll(lambda p: Implies("
             "0 <= p and p <= m, L[p][0] == 1))"),
        ],
        "g@L1":   ["j <= n"],
        "phi@L1": ["n - j + 1"],

        # Inner body: L[i][j] := L[i-1][j] + L[i][j-1]; j := j+1.
        "s@B2": [{
            "L": "Update(L, i, j, L[i-1][j] + L[i][j-1])",
            "j": "j + 1",
        }],

        "s@B3": [{"i": "i + 1"}],
        "s@B4": [{"result": "L[m][n]"}],
    },
    max_solutions = 1,
    solver_timeout_ms = 1_800_000,   # 30 min
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
