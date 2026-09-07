"""intdiv — Phase 3.N: integer division by repeated subtraction.

Computes q, r such that x == q*y + r and 0 <= r < y.

    q := 0
    r := x
    while (r >= y) {
        q := q + 1
        r := r - y
    }
    // post: x == q*y + r  ∧  0 <= r  ∧  r < y

The bilinear invariant `x == q*y + r` is the same shape as `mul.py`
(which goes the other direction, computing c := a*b).  This
benchmark exercises Z3's reasoning on `q*y` as a free-variable
product, similar to IntSqrt's `i*i`.

Proof witness:
    τ : x == q*y + r  ∧  r >= 0  ∧  q >= 0  ∧  y > 0
    ϕ : r
    g : r >= y

Spec:
    Pre  : y > 0  ∧  x >= 0
    Post : x == q*y + r  ∧  0 <= r  ∧  r < y
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1)),
    inputs   = [Var("x", "int", "input"), Var("y", "int", "input")],
    outputs  = [Var("q", "int", "output"), Var("r", "int", "output")],
    pre      = "y > 0 and x >= 0",
    post     = "x == q*y + r and 0 <= r and r < y",

    atoms = {
        "s@B0": [
            {"q": "0",   "r": "x"},            # published
            {"q": "x",   "r": "0"},            # wrong direction
            {"q": "0",   "r": "0"},            # forgets initial r := x
        ],
        "tau@L0": [
            "x == q*y + r",                    # published
            "r >= 0",                          # published
            "q >= 0",                          # published
            "y > 0",                           # published — preserved from Pre
            "r == x",                          # distractor — only initial
            "q == 0",                          # distractor — only initial
        ],
        "g@L0": [
            "r >= y",                          # published
            "r > y",                           # off-by-one
            "r > 0",                           # too weak — would over-subtract
        ],
        "phi@L0": [
            "r",                               # published — decreases by y each iter
            "q",                               # wrong direction — increases
            "x - r",                           # increases, not decreases
        ],
        "s@B1": [
            {"r": "r - y", "q": "q + 1"},      # published
            {"r": "r - 1", "q": "q + 1"},      # wrong: r decreases by 1
            {"r": "r - y", "q": "q"},          # forgets q increment
        ],
    },
    max_solutions = 5,        # bumped from 3 so the search covers
                               # all new variants under Fpre propagation.
    expected_solutions = 4,    # 2 -> 4 after Phase Fpre-Sym (2026-06-08):
                               # `y > 0` and `q >= 0` now provably
                               # preserved when Fpre propagates into the
                               # inductive antecedent.  Full set: base
                               # τ; +`y > 0`; +`q >= 0`; +both.  Sound.
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
