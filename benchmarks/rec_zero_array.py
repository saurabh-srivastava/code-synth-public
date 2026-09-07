"""rec_zero_array — Phase 3.F benchmark, Recur top-level template.

Synthesize a recursive procedure that zeros out the first n elements
of an array:

    def f(A, n):
        f(A, n - 1);             // recursive call on n-1
        A[n - 1] := 0;           // set the n-th element

Template: a single `Recur`.  The acyclic post-processing step
(`A[n-1] := 0`) is folded into the recur atom's `ret` expression as
`Update(A, n - 1, 0)` — the `ret` binding lets the expression read
the returned A and use the pre-state n to compute the index.

This is structurally `~` (just one rec call) rather than POPL'10's
`~;◦`, because chaining `Recur >> SB` cleanly needs an intermediate
binding (not yet supported by the constraint generator's
single-pre/single-post design).

No conditional branching — the base case is handled implicitly by
the spec's vacuous truth when n = 0 (same trick as POPL'10's
MergeSort/QuickSort with empty subranges).

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  A[k] == 0

Termination: ϕ_proc = n (decreases by 1 per recursive call).

Why the base case is vacuous: at n = 0 the recursive call's args
have `n_arg = -1`, where Fpre(n_arg) = `n_arg >= 0` is false.  The
induction hypothesis is then vacuously true, leaving the call's
returned A unconstrained.  The procedure's own post for n = 0 is
`∀k. 0 <= k < 0 ⇒ ...` which is trivially true regardless of A.
"""
from synth import Problem, SB, Loop, Recur, Var, solve


PROBLEM = Problem(
    template = Recur(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",

    atoms = {
        # Recur transition: rec call on (A, n - 1); the post-processing
        # step (A[n-1] := 0) is encoded in the `ret` expression.  `A`
        # in `ret` refers to the *returned* A from the call; `n` is the
        # procedure's pre-state n.
        "s@R0": [
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},           # published — decreasing n
             "ret":  {"A": "Update(A, n - 1, 0)"}},
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},
             "ret":  {"A": "Update(A, n, 0)"}},          # wrong index
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},
             "ret":  {"A": "A"}},                        # no post-processing (wrong)
            {"_recur": True,
             "args": {"A": "A", "n": "n"},               # no decrease — fails phi
             "ret":  {"A": "Update(A, n - 1, 0)"}},
        ],
        # Procedure ranking function.
        "phi@PROC": [
            "n",                                         # published
            "0",
        ],
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
