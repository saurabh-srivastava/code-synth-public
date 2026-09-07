"""matrix_diagonal_sum — Phase 3.S 2D follow-up.

Compute the sum of the main diagonal of an n×n integer matrix:

    result := 0
    i := 0
    while (i < n):
        result := result + A[i][i]
        i := i + 1
    // post: result == diag_sum(A, n, n)

The post is stated in terms of an uninterpreted function
`diag_sum : (Int → Int → Int) → Int → Int → Int` representing
`A[0][0] + A[1][1] + ... + A[k-1][k-1]` for the first k diagonal
elements.  Axioms:

    diag_sum(A, n, 0)        = 0
    diag_sum(A, n, k + 1)    = diag_sum(A, n, k) + A[k][k]     (k ≥ 0)

This is the 2D analogue of `sum_array`: same control flow, but the
array argument is `int[][]` and the per-step term is `A[i][i]`
(2D indexing).  First agent-authored 2D-array benchmark with a UF
spec — exercises:

  • `int[][]` Var declaration and lowering to `Int → Int → Int`.
  • Atom-string syntax `A[i][i]` (parses to nested `Select`).
  • UF arg-type `int[][]` lowered with proper parenthesisation
    in the Lean signature.
  • Recurrence axiom mentioning `A[k][k]`.
  • Tier-3 helpers for sc0 (entry-bundle UF cliff per F14),
    sc1 (loop-inductive with 2D recurrence), and sc4
    (chain-bundle post).

Spec:
    Pre  : n ≥ 0
    Post : result == diag_sum(A, n, n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an n×n integer matrix A and a length n (with n ≥ 0), "
        "return the sum of the main diagonal: "
        "A[0][0] + A[1][1] + ... + A[n-1][n-1]."
    ),

    template = SB(n=1) >> Loop(SB(n=1)),
    inputs   = [Var("A", "int[][]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [
        ("diag_sum", ["int[][]", "int", "int"], "int"),
    ],
    axioms = [
        # Base: empty diagonal sum is 0.
        "diag_sum(A, n, 0) == 0",
        # Recurrence: extend by one diagonal element.
        ("ForAll(lambda k: Implies(k >= 0, "
         "diag_sum(A, n, k + 1) == diag_sum(A, n, k) + A[k][k]))"),
    ],

    pre  = "n >= 0",
    post = "result == diag_sum(A, n, n)",

    atoms = {
        # SB0: result, i := 0, 0
        "s@B0": [{"result": "0", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "result == diag_sum(A, n, i)",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Loop body: result := result + A[i][i]; i := i + 1.
        "s@B1": [{"result": "result + A[i][i]", "i": "i + 1"}],
    },

    max_solutions = 1,
    expected_solutions = 1,
    # Axiom-heavy; Lean fallthrough expected on sc0 (entry-bundle
    # UF cliff per F14) and sc1 (recurrence).
    expected_lean_hits = 0,
    solver_timeout_ms = 1_800_000,   # 30 min, axiom-heavy + 2D
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/matrix_diagonal_sum",
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
