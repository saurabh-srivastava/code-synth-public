"""lcs — Phase 3.S: longest common subsequence DP.

**Known timeout** (>20 min, 2026-05-14).  Documented research
data point, **not in the regression suite**.

Classical 2D DP for the longest common subsequence of two strings.
Uses the native `int[][]` IR type added in Phase 3.S — sidesteps
the quantified-nonlinear-arithmetic wall that the 1D-flattened
version hit (Z3 couldn't reason about `p*n+q == i*n+j` under
universal quantifiers).  Once the polynomial-index wall is gone,
the next wall — axiom-heavy 2D DP with UF recurrences — emerges.
Sibling `grid_paths.py` shows the same wedge without the
case-split, so the LCS-specific complexity isn't the dominant
factor; it's the combination of 2D arrays + UF + recurrence axiom
+ quantified invariants that exceeds Z3's per-class budget.

    i := 1
    while (i <= m):
        j := 1
        while (j <= n):
            if X[i-1] == Y[j-1]:
                L[i][j] := L[i-1][j-1] + 1
            else:
                L[i][j] := max(L[i-1][j], L[i][j-1])
            j := j + 1
        i := i + 1
    result := L[m][n]
    // post: result == lcs(m, n)

`lcs(i, j)` is an uninterpreted function specifying the length of
the longest common subsequence of X[0..i) and Y[0..j).  Its
recurrence is supplied as axioms — the synthesizer fills the DP
table so that `L[i][j] == lcs(i, j)` and reads the answer off
`L[m][n]`.

Encoding decisions
------------------
- **L is pre-zeroed.**  Pre asserts `∀p, q. 0 ≤ p ≤ m ∧ 0 ≤ q ≤ n
  ⇒ L[p][q] == 0`.  Both base cases (`lcs(0, j) = 0` and
  `lcs(i, 0) = 0`) follow trivially.
- **Column 0 preserved.**  No transition writes to a cell with
  `j = 0`, so column 0 stays zero throughout.  τ_outer / τ_inner
  carry an explicit `∀p. 0 ≤ p ≤ m ⇒ L[p][0] == 0` atom.
- **Recurrence axioms split** by the `X[i-1] == Y[j-1]` case.

Spec:
    Pre  : m ≥ 0 ∧ n ≥ 0 ∧ L pre-zeroed on [0..m] × [0..n]
    Post : result == lcs(m, n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = (
        SB(n=1)
        >> Loop(
            SB(n=1)
            >> Loop(SB(n=2))
            >> SB(n=1)
        )
        >> SB(n=1)
    ),
    inputs = [
        Var("m", "int", "input"),
        Var("n", "int", "input"),
        Var("X", "int[]", "input"),
        Var("Y", "int[]", "input"),
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

    uninterpreted = [
        ("lcs", ["int", "int"], "int"),
    ],
    axioms = [
        "ForAll(lambda j: Implies(j >= 0, lcs(0, j) == 0))",
        "ForAll(lambda i: Implies(i >= 0, lcs(i, 0) == 0))",
        ("ForAll(lambda i, j: Implies("
         "i >= 1 and j >= 1 and X[i-1] == Y[j-1], "
         "lcs(i, j) == lcs(i-1, j-1) + 1))"),
        ("ForAll(lambda i, j: Implies("
         "i >= 1 and j >= 1 and X[i-1] != Y[j-1], "
         "lcs(i, j) == (lcs(i-1, j) if lcs(i-1, j) >= lcs(i, j-1) "
         "else lcs(i, j-1))))"),
    ],

    pre = ("m >= 0 and n >= 0 and "
           "ForAll(lambda p, q: Implies("
           "0 <= p and p <= m and 0 <= q and q <= n, L[p][q] == 0))"),
    post = "result == lcs(m, n)",

    atoms = {
        # SB0: i := 1.
        "s@B0": [{"i": "1"}],

        # Outer τ.
        "tau@L0": [
            "1 <= i",
            "i <= m + 1",
            "m >= 0",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p < i and 0 <= q and q <= n, "
             "L[p][q] == lcs(p, q)))"),
            ("ForAll(lambda p: Implies("
             "0 <= p and p <= m, L[p][0] == 0))"),
        ],
        "g@L0":   ["i <= m"],
        "phi@L0": ["m - i + 1"],

        # SB1: j := 1.
        "s@B1": [{"j": "1"}],

        # Inner τ.
        "tau@L1": [
            "1 <= i", "i <= m",
            "1 <= j", "j <= n + 1",
            "m >= 0", "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p < i and 0 <= q and q <= n, "
             "L[p][q] == lcs(p, q)))"),
            ("ForAll(lambda q: Implies("
             "0 <= q and q < j, "
             "L[i][q] == lcs(i, q)))"),
            ("ForAll(lambda p: Implies("
             "0 <= p and p <= m, L[p][0] == 0))"),
        ],
        "g@L1":   ["j <= n"],
        "phi@L1": ["n - j + 1"],

        # Inner body SB(n=2): match / mismatch.
        "g@B2.0": ["X[i-1] == Y[j-1]"],
        "s@B2.0": [{
            "L": "Update(L, i, j, L[i-1][j-1] + 1)",
            "j": "j + 1",
        }],
        "g@B2.1": ["X[i-1] != Y[j-1]"],
        "s@B2.1": [{
            "L": ("Update(L, i, j, "
                  "L[i-1][j] if L[i-1][j] >= L[i][j-1] "
                  "else L[i][j-1])"),
            "j": "j + 1",
        }],

        # SB3: i := i + 1.
        "s@B3": [{"i": "i + 1"}],

        # SB4: result := L[m][n].
        "s@B4": [{"result": "L[m][n]"}],
    },
    max_solutions = 1,
    solver_timeout_ms = 3_600_000,   # 60 min
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
