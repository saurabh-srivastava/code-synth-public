"""nested_loop — Phase 3.K: doubly-nested counter (first nested-Loop benchmark).

Template `SB; Loop( SB; Loop(SB); SB )`:

    i := 0;
    while (i < n) {                  // outer L0
        j := 0;
        while (j < n) {              // inner L1
            j := j + 1;
        }
        i := i + 1;
    }
    // post: i == n

The inner loop does nothing useful — it's there to exercise the
nested-Loop machinery.  The outer Loop's body is `SB(n=1) >>
Loop(SB(n=1)) >> SB(n=1)` (a non-SB template), so the constraint
generator takes the Phase 3.K recursive `walk_template` path.

Proof witness:
    τ_outer : i <= n  ∧  i >= 0  ∧  n >= 0
    ϕ_outer : n - i
    τ_inner : j >= 0  ∧  j <= n  ∧  i < n  ∧  i >= 0  ∧  n >= 0
    ϕ_inner : n - j

The frame fix is load-bearing here: the outer ranking decrease
`ϕ_outer(body_in_L0) > ϕ_outer(body_out_L0)` would otherwise be
unprovable, since the inner Loop's abstract transition leaves
`i` and `n` unconstrained relative to outer-entry values.  Phase
3.K adds preservation equations `v_after_loop == v_before_loop`
for vars not in the loop body's modified set.

Spec:
    Pre  : n >= 0
    Post : i == n
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1) >> Loop(SB(n=1)) >> SB(n=1)),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("i", "int", "output")],
    locals   = [Var("j", "int", "local")],
    pre      = "n >= 0",
    post     = "i == n",

    atoms = {
        # SB0 — initial i := 0.
        "s@B0": [
            {"i": "0"},                # published
            {"i": "n"},                # would skip outer loop entirely
        ],
        # Outer loop L0.
        "tau@L0": [
            "i <= n",                  # published
            "i >= 0",                  # published
            "n >= 0",                  # published — needed for ϕ_outer LB
        ],
        "g@L0": [
            "i < n",                   # published
            "i <= n",                  # doesn't terminate
        ],
        "phi@L0": [
            "n - i",                   # published
            "i",                       # wrong direction
        ],
        # SB1 — inner init j := 0.
        "s@B1": [
            {"j": "0"},                # published
            {"j": "n"},                # would skip inner loop
        ],
        # Inner loop L1.  Atoms include preservation conjuncts (i < n,
        # i >= 0, n >= 0) so the outer-body post-Loop bundle can derive
        # τ_outer after `i := i + 1`.
        "tau@L1": [
            "j >= 0",                  # published
            "j <= n",                  # published
            "i < n",                   # published — preserves outer guard
            "i >= 0",                  # published — preserves outer i>=0
            "n >= 0",                  # published
        ],
        "g@L1": [
            "j < n",                   # published
            "j <= n",                  # doesn't terminate
        ],
        "phi@L1": [
            "n - j",                   # published
            "j",                       # wrong direction
        ],
        # SB2 — inner body j := j + 1.
        "s@B2": [
            {"j": "j + 1"},            # published
            {"j": "j"},                # no progress
        ],
        # SB3 — outer step i := i + 1.
        "s@B3": [
            {"i": "i + 1"},            # published
            {"i": "i"},                # no progress
        ],
    },
    max_solutions = 3,
    expected_solutions = 3,
    expected_lean_hits = 0,
    solver_timeout_ms = 180_000,
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
