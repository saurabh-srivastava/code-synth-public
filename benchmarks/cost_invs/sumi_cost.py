"""sumi_cost — first cost-bound synthesis benchmark.

Same shape as `sumi`, but with `cost_target = "N"` and a
`cost@L0` hole.  Validates that the COST_INVS §1 plumbing
(cost@L hole allocation + (A)(B)(C) constraint emission)
works end-to-end against the synth framework.

Expected outcome:
  - cost@L0 = "N - i" is the correct choice (decreases by 1
    per iteration, starts at N, ends at 0).
  - All three obligations close:
      (A) τ ⇒ cost@L0 ≥ 0       — true at every reachable state.
      (B) τ ∧ g ∧ trans ⇒
            cost@L0(pre) ≥ 1 + cost@L0(post)   — decreases by 1.
      (C) Pre ⇒ cost@L0(initial) ≤ cost_target = N — initial cost
            at i=0 is N - 0 = N, target is N.  Tight equality.
  - Synth returns a solution with `cost@L0 = N - i`.

Distractor candidates for cost@L0:
  - "N"      — constant; fails (B) (decrement requires actual
               decrease).
  - "i"      — increasing; fails (B) (decrease direction wrong).
  - "N - i - 1" — fails (A) at N=0 (cost = -1 < 0).
  - "N + 1 - i" — works for (A) and (B) but fails (C):
               cost@L0(0) = N + 1, target = N → N + 1 ≤ N FALSE.
  - "N - i"  — published, works.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("N", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "N >= 0",
    post     = "2*s == N*(N + 1)",
    cost_target = "N",                  # ← NEW: COST_INVS §1
    atoms = {
        "tau@L0": [
            "2*s == i*(i + 1)",
            "0 <= i",
            "i <= N",
        ],
        "g@L0": [ "i < N" ],
        "phi@L0": [ "N - i" ],
        # NEW: cost@L0 candidate list.
        "cost@L0": [
            "N - i",        # ← published; expected pick
            "N",            # fails (B): cost(pre) - cost(post) = 0, not ≥ 1
            "i",            # fails (B): cost decreases wrong direction
            "N - i - 1",    # fails (A) at N=0
            "N + 1 - i",    # fails (C): initial cost N+1 > target N
        ],
        "s@B0": [ {"s": "0", "i": "0"} ],
        "s@B1": [ {"s": "s + i + 1", "i": "i + 1"} ],
        "s@B2": [ {} ],
    },
    max_solutions = 3,
    expected_solutions = 2,   # 2 valid τ subsets × 1 valid cost@L0 = 2.
    expected_lean_hits = 0,
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
