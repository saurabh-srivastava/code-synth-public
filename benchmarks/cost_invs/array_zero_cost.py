"""array_zero_cost — second cost-bound synthesis benchmark.

Same shape as `array_zero`, with `cost_target = "n"` and a
`cost@L0` hole.  Verifies that COST_INVS §1 works on an array-
writing loop (different from sumi's scalar accumulation).

Loop:  while (i < n) { A[i] := 0; i := i + 1 }
Cost target: n.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] == 0))",
    cost_target = "n",
    atoms = {
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "ForAll(lambda p: Implies(0 <= p and p < i, A[p] == 0))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "cost@L0": [
            "n - i",         # ← published
            "n",             # fails (B)
            "n - i - 1",     # fails (A) at n=0
            "n + 1 - i",     # fails (C)
        ],
        "s@B0": [{"i": "0"}],
        "s@B1": [{"A": "Update(A, i, 0)", "i": "i + 1"}],
    },
    max_solutions = 3,
    expected_solutions = 2,
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
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
