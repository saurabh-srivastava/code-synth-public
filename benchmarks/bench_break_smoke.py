"""bench_break_smoke — K.B.IMPL-6: smoke test for the break primitive.

The first benchmark to exercise the `_break: True` transition-atom
flag end-to-end.  Algorithm: find the smallest non-negative `i`
such that `2*i >= threshold`; bail at `n` if not found.

  i := 0
  result := -1
  while i < n:
      if 2*i >= threshold:
          result := i
          break              -- exits the loop
      elif 2*i < threshold:
          i := i + 1

Post-condition holds either way:
  - Normal exit (i = n, result = -1): satisfied via `result == -1`.
  - Break exit (2*i ≥ threshold, result = i): satisfied via
    `2*result ≥ threshold` AND `result < n` (from i < n loop guard).

τ = {0 ≤ i, i ≤ n, result == -1} — the loop's invariant.  `result
== -1` is preserved while looping (branch 1 doesn't touch result);
violated at the break exit (where we set result := i) but the
break-bundle obligation in IMPL-3 doesn't check τ-preservation for
break branches.

What this validates:
  - K.B.IMPL-1 expand-time validation accepts the well-placed flag.
  - K.B.IMPL-2 skips τ-preservation + ranking-decrease for branch 0.
  - K.B.IMPL-3 emits a break-bundle obligation for branch 0.
  - K.B.IMPL-4's Lean translator dispatches to theorem_for_break_bundle.
  - K.B.IMPL-5's emitters render `break` in the synthesized code.

If this benchmark synthesizes a verified solution, the primitive is
working end-to-end and K.3.2 (concrete length-3 AP detection) is
unblocked.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("n", "int", "input"),
                Var("threshold", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0 and threshold >= 0",
    post     = (
        "(result == -1 or result < n) and "
        "(result == -1 or 2*result >= threshold)"
    ),
    atoms = {
        # Initialize.
        "s@B0": [{"i": "0", "result": "0 - 1"}],

        # Loop invariant.  result == -1 is the "haven't broken yet"
        # invariant; preserved by branch 1, violated at branch 0's
        # break-exit (but τ-preservation is skipped for break by IMPL-2).
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "result == -1",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: condition met → set result and break.
        "g@B1.0": ["2 * i >= threshold"],
        "s@B1.0": [{"result": "i", "_break": True}],

        # Branch 1: condition not met → continue.
        "g@B1.1": ["2 * i < threshold"],
        "s@B1.1": [{"i": "i + 1"}],

        # Final SB: identity (result is already correct on either
        # exit path).
        "s@B2": [{"result": "result"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/break_smoke",
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
    for k, sol in enumerate(result.solutions[:1]):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
