"""sumi_cost_bad — same as sumi_cost but with ONLY invalid cost@L0
candidates.  Expected: NoSolution (synth correctly rejects all
candidates because none satisfy the (A)(B)(C) obligations).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("N", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "N >= 0",
    post     = "2*s == N*(N + 1)",
    cost_target = "N",
    atoms = {
        "tau@L0": ["2*s == i*(i + 1)", "0 <= i", "i <= N"],
        "g@L0": ["i < N"],
        "phi@L0": ["N - i"],
        # ONLY bad candidates — all should fail (A), (B), or (C).
        "cost@L0": [
            "N",            # fails (B): no decrement
            "i",            # fails (B): wrong direction
            "N - i - 1",    # fails (A): N=0 → -1
            "N + 1 - i",    # fails (C): initial cost N+1 > target N
        ],
        "s@B0": [{"s": "0", "i": "0"}],
        "s@B1": [{"s": "s + i + 1", "i": "i + 1"}],
        "s@B2": [{}],
    },
    max_solutions = 3,
    expected_solutions = 0,
    expected_lean_hits = 0,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
    if result:
        print(f"UNEXPECTED SAT: {len(result.solutions)} solutions found.")
        for sol in result.solutions:
            print(sol.code)
        raise SystemExit(1)
    print(f"Expected NoSolution: {result.reason}")
