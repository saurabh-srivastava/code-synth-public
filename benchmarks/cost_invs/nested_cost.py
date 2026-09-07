"""nested_cost — first cost-bound NESTED-loop benchmark.

Same template as benchmarks/nested_loop.py with cost_target added:

    i := 0;
    while (i < n) {                  // outer L0
        j := 0;
        while (j < n) {              // inner L1
            j := j + 1;
        }
        i := i + 1;
    }

Per outer iteration:
  SB1 (j := 0)           cost 1
  Loop inner             cost = cost@L1(j=0) = n
  SB3 (i := i + 1)       cost 1
Total per-iter body cost = n + 2.

Outer cost = (n - i) iterations × (n + 2) per-iter cost
           = (n - i) * (n + 2).
At i = 0: n * (n + 2) = n² + 2n.

cost_target = "n * (n + 2)" — captures the full nested cost.

Exercises COST_INVS §1.5: when outer Loop has non-SB body
(Seq(SB, Loop, SB)), the cost-decrement constraint integrates
the inner loop's cost via the per-item body-cost composition
in walk_template.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1) >> Loop(SB(n=1)) >> SB(n=1)),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("i", "int", "output")],
    locals   = [Var("j", "int", "local")],
    pre      = "n >= 0",
    post     = "i == n",
    cost_target = "n * (n + 2)",
    atoms = {
        "s@B0": [{"i": "0"}],
        "tau@L0": [
            "i <= n",
            "i >= 0",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "cost@L0": [
            "(n - i) * (n + 2)",  # ← published quadratic
            "n - i",              # too small for cost-decrement
            "n * n",              # constant; fails (B)
        ],
        "s@B1": [{"j": "0"}],
        "tau@L1": [
            "j >= 0",
            "j <= n",
            "i < n",
            "i >= 0",
            "n >= 0",
        ],
        "g@L1":   ["j < n"],
        "phi@L1": ["n - j"],
        "cost@L1": [
            "n - j",              # ← published
            "n",                  # fails (B) (constant)
        ],
        "s@B2": [{"j": "j + 1"}],
        "s@B3": [{"i": "i + 1"}],
    },
    max_solutions = 3,
    expected_solutions = None,   # leave open until we see what Z3 returns
    expected_lean_hits = 0,
    solver_timeout_ms = 300_000,
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
