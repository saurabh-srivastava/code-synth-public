"""nested_zero_array — Phase 3.M: nested loops + array writes.

Outer loop writes A[i] := 0 each iteration; inner loop is a no-op
that just counts j to i.  Tests Phase 3.K's frame preservation: the
inner Loop's modified-vars set is {j}, so the abstract Loop
transition must carry `A`, `i`, `n` through unchanged for the outer
body's induction to close.

    i := 0;
    while (i < n) {
        A[i] := 0;
        j := 0;
        while (j < i) {
            j := j + 1;
        }
        i := i + 1;
    }
    // post: ∀k. 0 ≤ k < n ⇒ A[k] == 0

Proof witness:
    τ_outer : 0 ≤ i  ∧  i ≤ n  ∧  n ≥ 0  ∧  (∀p. 0 ≤ p < i ⇒ A[p] == 0)
    ϕ_outer : n - i
    τ_inner : 0 ≤ j  ∧  j ≤ i  ∧  i < n  ∧  n ≥ 0
    ϕ_inner : i - j

The inner τ is intentionally LIGHT — purely counter atoms, no array
predicates.  The outer body's final bundle derives the new zero-
prefix `∀p. 0 ≤ p < (i+1) ⇒ A[p] == 0` directly from:
  (a) outer τ's `∀p. 0 ≤ p < i ⇒ A[p] == 0`  (zero prefix at body_in),
  (b) SB1.trans:  A_state1 = Update(A_in, i_in, 0)  (writes A[i] := 0),
  (c) Loop1.abstract:  frame_eqs preserve A, i, n through inner,
  (d) SB3.trans:  i_body_out = i_state2 + 1.

(b) + (c) give `A_body_out = Update(A_in, i_in, 0)`; (d) gives
`i_body_out = i_in + 1`; combined with (a), the zero-prefix extends
to `< i_in + 1` (the i_in slot is fresh-zeroed by Update, earlier
slots inherit from outer τ).  No inner-τ array atom needed.

This also keeps τ_inner's atom count to 4 — 2^4 = 16 enumerated
subsets for the inner inductive constraint, vs 2^7 = 128 with the
array atoms included.

Spec:
    Pre  : n ≥ 0
    Post : ForAll(lambda k: Implies(0 ≤ k < n, A[k] == 0))
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1) >> Loop(SB(n=1)) >> SB(n=1)),
    inputs   = [Var("n", "int", "input"), Var("A", "int[]", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local"), Var("j", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",

    atoms = {
        "s@B0":   [{"i": "0"}],
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            "ForAll(lambda p: Implies(0 <= p and p < i, A[p] == 0))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1":   [{"A": "Update(A, i, 0)", "j": "0"}],
        "tau@L1": [
            "0 <= j",
            "j <= i",
            "i < n",
            "n >= 0",
        ],
        "g@L1":   ["j < i"],
        "phi@L1": ["i - j"],

        "s@B2":   [{"j": "j + 1"}],
        "s@B3":   [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 300_000,
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
