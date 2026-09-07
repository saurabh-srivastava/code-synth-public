"""max_array_cost — cost-bound variant of max_array.

Loop computing max over A[0..n).  cost_target = "n".
Validates COST_INVS §1 on a benchmark with branched SB(n=2) body
plus quantified array invariant.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 1",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= m))",
    cost_target = "n",
    atoms = {
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "ForAll(lambda k: Implies(0 <= k and k < i, A[k] <= m))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "cost@L0": [
            "n - i",         # ← published
            "n",             # fails (B)
            "n - i - 1",     # fails (A) at i=n (or boundaries)
        ],
        "s@B0":   [{"m": "0", "i": "0"}],
        "g@B1.0": ["A[i] > m"],
        "g@B1.1": ["A[i] <= m"],
        "s@B1.0": [{"m": "A[i]", "i": "i + 1"}],
        "s@B1.1": [{"i": "i + 1"}],
        "s@B2":   [{}],
    },
    max_solutions = 5,
    expected_solutions = None,
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
    for k, sol in enumerate(result.solutions[:3]):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
