"""cover_loop_branched_recur — soundness coverage benchmark.

Synthetic procedure designed to exercise the SB-body-of-Loop fast
path's missing per-procedure-decrease emission.  The algorithm:

    while (n > 0):
        if (n == 5):
            proc(n - 1)   # recursive call from inside loop body
        else:
            n := n - 1
    // post: n == 0

Pre `n >= 0`.  Post `n == 0`.

The recur branch's published atom uses `args = {n: n - 1}` (strictly
decreasing) with `ret = {n: n}` (the call's final n is 0 by IH,
which becomes the outer n, then the loop exits).

A DEGENERATE alternative atom is included: `args = {n: n}` with
`phi@PROC: 1` available.  This atom is logically unsound — it
recurses without decreasing — but cheaper by atom-complexity score,
so the synthesizer would prefer it IF the per-procedure-decrease
constraint isn't asserted at this context.

Expected behavior:
  - Before the structural refactor that emits SB-body-of-Loop
    per-procedure decreases: synthesizer accepts the degenerate
    atom, compiled C stack-overflows at runtime.
  - After: synthesizer rejects the degenerate atom and picks the
    decreasing `args = {n: n - 1}` instead.

The benchmark is contrived — there's no real-world reason to do a
recursive call inside a loop body — but the structural pattern
(SB(n>1) as a Loop body, one branch with a `_recur` atom) is what
matters for testing the constraint emission.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = Loop(SB(n=2)),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("n", "int", "output")],
    pre      = "n >= 0",
    post     = "n == 0",

    atoms = {
        "tau@L0": ["n >= 0"],
        "g@L0":   ["n > 0"],
        "phi@L0": ["n"],

        # Branch 0: n == 5 → recur with smaller arg (or, if the soundness
        # bug is alive, NON-decreasing arg).
        "g@B0.0": ["n == 5"],
        "s@B0.0": [
            {"_recur": True,
             "args":   {"n": "n - 1"},        # published — decreases
             "ret":    {"n": "n"}},
            {"_recur": True,
             "args":   {"n": "n"},            # degenerate — no decrease
             "ret":    {"n": "n"}},
        ],

        # Branch 1: else → simple decrement.
        "g@B0.1": ["n != 5"],
        "s@B0.1": [{"n": "n - 1"}],

        # Procedure ranking: "n" (decreases) or "1" (constant, never
        # decreases).  With the soundness bug, "1" would be picked
        # alongside the non-decreasing args because phi-decrease
        # isn't enforced for the SB-branch recur atom.
        "phi@PROC": ["n", "1"],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 120_000,
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
        # Print the chosen recur atom so the test can tell whether
        # the synthesizer picked the sound or degenerate option.
        recur_atom = sol.atoms.get("s@B0.0")
        if isinstance(recur_atom, dict) and recur_atom.get("_recur"):
            print(f"  picked recur args: {recur_atom.get('args')}")
            print(f"  picked phi@PROC:   {sol.atoms.get('phi@PROC')}")
