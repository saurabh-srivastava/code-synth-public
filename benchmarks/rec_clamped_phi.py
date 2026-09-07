"""rec_clamped_phi — Phase 3.J demonstration.

Same program as `rec_zero_array.py` but with the procedure ranking
function offered ONLY as a *clamped* expression `n if n > 0 else 0`.
This ϕ would have failed Phase 3.E.2's unconditional decrease
constraint at the base case:

    For n = 0 (procedure inputs, satisfying Fpre `n >= 0`):
        rec args.n = -1, ϕ(in) = 0, ϕ(args) = 0.
        decrease: 0 > 0 → FALSE.

Phase 3.J's relaxation `current_pre ∧ b_recur ∧ Fpre(args)
⇒ ϕ(in) > ϕ(args)` gates the decrease on Fpre(args).  At n = 0,
args.n = -1 violates Fpre — IH is vacuous — and decrease is not
required.  The clamped ϕ is therefore accepted.

This is the POPL'10 vacuous-base-case ranking pattern (MergeSort
with empty subranges, etc.).

Spec:
    Pre  : n >= 0
    Post : ForAll k. 0 <= k < n  ⇒  A[k] == 0
"""
from synth import Problem, Recur, Var, solve


PROBLEM = Problem(
    template = Recur(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",

    atoms = {
        "s@R0": [
            {"_recur": True,
             "args": {"A": "A", "n": "n - 1"},
             "ret":  {"A": "Update(A, n - 1, 0)"}},
            {"_recur": True,
             "args": {"A": "A", "n": "n"},           # no decrease
             "ret":  {"A": "Update(A, n - 1, 0)"}},
        ],
        # ONLY the clamped ϕ candidate — no `n` fallback.
        # Without Phase 3.J this benchmark would be UNSAT.
        "phi@PROC": [
            "n if n > 0 else 0",                     # clamped
        ],
    },
    max_solutions = 3,
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
