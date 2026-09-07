"""rec_const — Phase 3.E minimum-viable recursion test.

Synthesize a recursive procedure that returns 0 for any n ≥ 0:

    def f(n):
        if (n <= 0)  result := 0;
        else         result := f(n - 1);

Template: `SB(n=2)` — single acyclic block with two branches.
Branch 0 = base case (TS atom); Branch 1 = recursive call (recur atom).

Spec:
    Pre  : n >= 0
    Post : result == 0

Recursive call encoding (POPL'10 §5.3):
    s_recur = s_args ∧ (Fpre(vin') ⇒ Fpost(vin', vout'')) ∧ s_ret

The synthesizer assumes the call satisfies the procedure's own spec
(the induction hypothesis).  Termination is a separate concern not
handled in this minimum-viable benchmark.
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    template = SB(n=2),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "n >= 0",
    post     = "result == 0",
    atoms = {
        # Branch 0 guard: base case "n <= 0".
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
        # Branch 0 transition: base case.
        "s@B0.0": [
            {"result": "0"},                                # published
            {"result": "n"},                                # wrong for n>0
        ],
        # Branch 1 (else) transition: recur with smaller arg.
        # The published recur atom: call self with n-1, take its `result`
        # as our `result`.
        "s@B0.1": [
            {"_recur": True,
             "args": {"n": "n - 1"},                        # smaller arg
             "ret":  {"result": "result"}},                 # identity ret
            {"_recur": True,
             "args": {"n": "n"},                            # no decrease (wrong; phi check rules out)
             "ret":  {"result": "result"}},
            {"result": "0"},                                # non-recur option: directly 0
            {"result": "n"},
        ],
        # Phase 3.E.2 procedure ranking function (single-hot).
        "phi@PROC": [
            "n",                                            # published — decreases each call
            "0",                                            # constant — fails decrease
            "1",                                            # constant — fails decrease
        ],
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
