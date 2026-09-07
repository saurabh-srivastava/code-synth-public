"""rec_zero_double — Phase 3.H validation of POPL'10's ~;~;◦ shape.

Template: `Recur >> Recur >> SB` — two recursive calls followed by an
acyclic post-processing step.  This is structurally MergeSort
(`~;~;◦` per POPL'10 §5.3) but with the zero-out logic from
`rec_zero_array` instead of merge/sort.

Both recursive calls have `args = (A, n-1)`; the first does the
actual work (zeroing A[0..n-2]) and the second is technically
redundant under the spec assumption (it also "zeros A[0..n-2]" —
which is already true).  The SB sets `A[n-1] := 0`.

The point of the benchmark is to validate the Phase 3.G bundled
chain on a 3-item template: state bindings s0→s1→s2→s3 with all
three transitions conjoined into one safety constraint, plus a
per-Recur decrease constraint at each call site.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  A[k] == 0
"""
from synth import Problem, SB, Recur, Var, solve


PROBLEM = Problem(
    template = Recur() >> Recur() >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",

    atoms = {
        # First rec call.
        "s@R0": [
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},          # published
             "ret":  {"A": "A"}},
            {"_recur": True,
             "args": {"A": "A", "n": "n"},              # no decrease
             "ret":  {"A": "A"}},
        ],
        # Second rec call.
        "s@R1": [
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},          # published
             "ret":  {"A": "A"}},
            {"_recur": True,
             "args": {"A": "A", "n": "n"},              # no decrease
             "ret":  {"A": "A"}},
        ],
        # Final post-processing SB.
        "s@B0": [
            {"A": "Update(A, n - 1, 0)"},               # published
            {"A": "Update(A, n, 0)"},                    # wrong index
            {"A": "A"},                                  # no-op
        ],
        # Procedure ranking.
        "phi@PROC": ["n", "0"],
    },
    max_solutions = 5,
    expected_solutions = 1,
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
