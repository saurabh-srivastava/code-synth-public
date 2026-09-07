"""cover_chain_branched_recur — regression guard for today's
SB-branch-decrease-in-chain fix.

Template: `Recur() >> SB(n=2)` — but the SECOND item (the SB) has a
recur atom in one branch.  Without today's fix to
`_emit_chain_recur_decreases` (which now iterates SB items and
emits per-branch decrease), the synthesizer would accept a
non-decreasing recur atom here.

Algorithm:

    proc(n):  # n is in/out
        proc(n - 1)            # top-level Recur item
        if (n > 0):
            proc(n - 1)        # SB-branch recur — second call
        else:
            n := 0             # base-case branch
    // post: n == 0

This is intentionally redundant (calling proc twice) — the point is
the structural pattern of an SB(n>1)-branch recur in a chain, not
the algorithm's value.

Both `_recur` atoms have a degenerate `args: {n: n}` alternative
that should be rejected by the per-procedure-decrease constraint.

Pre `n >= 0`.  Post `n == 0`.
"""
from synth import Problem, SB, Loop, Recur, Var, solve


PROBLEM = Problem(
    template = Recur() >> SB(n=2),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("n", "int", "output")],
    pre      = "n >= 0",
    post     = "n == 0",

    atoms = {
        # Top-level Recur — already protected by today's fix.
        "s@R0": [
            {"_recur": True,
             "args":   {"n": "n - 1"},        # published
             "ret":    {"n": "n"}},
            {"_recur": True,
             "args":   {"n": "n"},            # degenerate
             "ret":    {"n": "n"}},
        ],

        # SB(n=2): branch 0 recur, branch 1 base case.
        "g@B0.0": ["n > 0"],
        "s@B0.0": [
            {"_recur": True,
             "args":   {"n": "n - 1"},        # published
             "ret":    {"n": "n"}},
            {"_recur": True,
             "args":   {"n": "n"},            # degenerate
             "ret":    {"n": "n"}},
        ],
        "g@B0.1": ["n <= 0"],
        "s@B0.1": [{"n": "0"}],

        "phi@PROC": ["n", "1"],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 60_000,
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
        print(f"  top-recur args: {sol.atoms['s@R0'].get('args')}")
        print(f"  SB-branch recur args: {sol.atoms['s@B0.0'].get('args')}")
        print(f"  phi@PROC: {sol.atoms.get('phi@PROC')}")
