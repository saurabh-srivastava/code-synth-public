"""bench_nested_break_smoke — K.D.IMPL-5: smoke for nested-Loop break.

Validates that K.D.IMPL-1/2/3/4 emit and discharge a break-bundle
obligation whose conclusion is `τ_enclosing(body_out)` instead of
`Fpost(body_out)` when the breaking Loop is nested inside another
Loop.

Algorithm:

  o := 0
  while o < n_outer:
      i, o := 0, o + 1     -- step outer counter, init inner
      while i < n_inner:
          if 2*i >= n_inner:
              break        -- inner break; exits inner only
          else:
              i := i + 1
      -- (no further outer-body items; falls through to outer τ check)
  result := o

The inner Loop is the LAST item in outer's body chain.  Therefore
the inner body's break-exit state IS the outer body's output
state, and τ_outer must hold there directly — no chain tail to
compose through.  (Chain-tail-after-break is K.D.2.a, deferred.)

Outer τ atoms — `0 ≤ o`, `o ≤ n_outer` — must hold at the inner
body's break-exit.  Inner τ carries these.  The break transition
modifies only inner-local vars; `o` is preserved via frame eq.

What this validates:
  - K.D.IMPL-1 detects the inner Loop's enclosing context.
  - K.D.IMPL-2 emits τ_enclosing at body_out (not Fpost).
  - K.D.IMPL-3 dispatches with enclosing_loop_id.
  - K.D.IMPL-4 emits the nested-flavored break-bundle theorem.
  - K.D break-Loop abstract transition drops `¬g` for the
    enclosing Loop's body-inductive obligation.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = (
        SB()
        >> Loop(SB() >> Loop(SB(n=2)))
        >> SB()
    ),
    inputs   = [Var("n_outer", "int", "input"),
                Var("n_inner", "int", "input")],
    outputs  = [Var("result",  "int", "output")],
    locals   = [Var("o", "int", "local"),
                Var("i", "int", "local")],
    pre      = "n_outer >= 0 and n_inner >= 0",
    post     = "result >= 0",
    atoms = {
        # B0 — outer init.
        "s@B0": [{"o": "0"}],

        # Outer Loop invariant.  `n_inner >= 0` and `n_outer >= 0`
        # need to be carried here because the recursive walk into
        # L0's body uses pre_fn = τ_outer ∧ g_outer (NOT Fpre), so
        # inner constraints can only rely on what τ_outer says.
        "tau@L0": [
            "0 <= o",
            "o <= n_outer",
            "n_inner >= 0",
            "n_outer >= 0",
        ],
        "g@L0":   ["o < n_outer"],
        "phi@L0": ["n_outer - o"],

        # B1 — step outer counter AND init inner.  Done together so
        # the inner Loop is the only remaining item in outer's body,
        # making inner-body_out the outer body's terminating state.
        "s@B1": [{"i": "0", "o": "o + 1"}],

        # Inner Loop invariant — carries outer τ atoms (post-increment).
        # After B1, o has been incremented, so the live invariant on
        # `o` is `1 <= o ≤ n_outer`.
        "tau@L1": [
            "0 <= i",
            "i <= n_inner",
            "1 <= o",
            "o <= n_outer",
        ],
        "g@L1":   ["i < n_inner"],
        "phi@L1": ["n_inner - i"],

        # Inner branch 0: condition met → break.  Modifies nothing;
        # outer's `o` is preserved by frame eq.
        "g@B2.0": ["2 * i >= n_inner"],
        "s@B2.0": [{"_break": True}],

        # Inner branch 1: condition not met → step inner counter.
        "g@B2.1": ["2 * i < n_inner"],
        "s@B2.1": [{"i": "i + 1"}],

        # B3 — final: result := o.  After outer exits normally,
        # o == n_outer ≥ 0.
        "s@B3": [{"result": "o"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 600_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/nested_break_smoke"
    ),
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
