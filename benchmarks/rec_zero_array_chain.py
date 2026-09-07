"""rec_zero_array_chain — Phase 3.G validation: `Recur >> SB`.

Same problem as `rec_zero_array.py` but expressed with a chained
template: a recursive call followed by an acyclic post-processing
step.  This is the POPL'10 `~;◦` shape — a building block for
sort-style benchmarks where the acyclic ◦ is the merge / partition
step that follows recursive calls.

The Phase 3.G refactor introduced per-checkpoint state bindings, so
the SB's pre-state is the Recur's post-state.  The two items' atoms
are *bundled* into a single safety constraint:

    Fpre(s_0) ∧ recur_trans(s_0, s_1) ∧ sb_trans(s_1, s_2)  ⇒  Fpost(s_2)

with `s_1` as a fresh intermediate state binding.  The verifier
treats `s_1` as a free var when checking attribute-class validity.

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  A[k] == 0
"""
from synth import Problem, SB, Recur, Var, solve


PROBLEM = Problem(
    template = Recur() >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",

    atoms = {
        # Recur transition: rec call on (A, n - 1); take the returned A.
        # NOTE the difference from rec_zero_array.py: here ret is the
        # identity (no post-processing) — the post-processing happens
        # in the chained SB.
        "s@R0": [
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},
             "ret":  {"A": "A"}},
            {"_recur": True,
             "args": {"A": "A", "n": "n"},                    # no decrease
             "ret":  {"A": "A"}},
        ],
        # Acyclic step: A := Update(A, n - 1, 0).
        "s@B0": [
            {"A": "Update(A, n - 1, 0)"},                     # published
            {"A": "Update(A, n, 0)"},                          # wrong index
            {"A": "A"},                                        # no-op
        ],
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
