"""rec_neg — Phase 3.E recursion with a non-identity ret transformation.

Synthesize a recursive procedure that returns -n for n ≥ 0:

    def f(n):
        if (n <= 0)  result := n;          // 0 at n=0
        else         result := f(n - 1) - 1;

The recursive case demonstrates the general `ret` shape:
`ret = {"result": "result - 1"}`  — the local `result` is set to the
call's returned `result` minus 1.  Decoded as

    (_r_result) := synth(n - 1);
    result := _r_result - 1;

Spec:
    Pre  : n >= 0
    Post : result == 0 - n      (i.e., -n)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    template = SB(n=2),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "n >= 0",
    post     = "result == 0 - n",
    atoms = {
        "g@B0.0": [
            "n <= 0",                                       # published
            "n == 0",
            "n < 0",
        ],
        # Phase 3.I: branch 1's explicit "else" guard.
        "g@B0.1": [
            "n > 0",                                        # published — the else
            "n >= 0",
            "n >= 1",
        ],
        # Base case: result := n (works when n = 0; n = -0 trivially).
        "s@B0.0": [
            {"result": "n"},                                # published
            {"result": "0"},
            {"result": "0 - n"},
        ],
        # Recursive case: result := f(n - 1) - 1.
        "s@B0.1": [
            {"_recur": True,
             "args": {"n": "n - 1"},
             "ret":  {"result": "result - 1"}},             # published
            {"_recur": True,
             "args": {"n": "n - 1"},
             "ret":  {"result": "result"}},                 # wrong (doesn't decrement)
            {"_recur": True,
             "args": {"n": "n - 1"},
             "ret":  {"result": "result + 1"}},             # wrong direction
        ],
        # Phase 3.E.2 procedure ranking function (single-hot).
        "phi@PROC": ["n", "0"],
    },
    max_solutions = 5,
    expected_solutions = 5,
    expected_lean_hits = 0,
    solver_timeout_ms = 60_000,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
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
