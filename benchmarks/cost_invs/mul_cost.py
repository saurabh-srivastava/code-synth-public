"""mul_cost — cost-bound variant of mul.

Single-loop multiplication via repeated addition.  cost_target = "b".
Same shape as mul; should pick cost@L0 = "b - i".
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("a", "int", "input"), Var("b", "int", "input")],
    outputs  = [Var("p", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "a >= 0 and b >= 0",
    post     = "p == a*b",
    cost_target = "b",
    atoms = {
        "tau@L0": [
            "p == a*i",
            "0 <= i",
            "i <= b",
        ],
        "g@L0":   ["i < b"],
        "phi@L0": ["b - i"],
        "cost@L0": [
            "b - i",       # ← published
            "b",           # fails (B)
            "b - i - 1",   # fails (A) at b=0
        ],
        "s@B0": [{"p": "0", "i": "0"}],
        "s@B1": [{"p": "p + a", "i": "i + 1"}],
        "s@B2": [{}],
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
