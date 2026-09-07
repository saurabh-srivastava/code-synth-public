"""power_of_two — Phase X corpus benchmark.

Compute 2^n for n ≥ 0 via iterative doubling.  Uses a UF `pow2`
with the standard recurrence.

Spec:
    Pre  : n >= 0
    Post : r == pow2(n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-negative integer n, return 2 raised to the n. "
        "I.e., 1 if n=0, 2 if n=1, 4 if n=2, and so on."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("pow2", ["int"], "int")],
    axioms = [
        "pow2(0) == 1",
        ("ForAll(lambda k: Implies(k >= 0, "
         "pow2(k + 1) == 2 * pow2(k)))"),
    ],

    pre  = "n >= 0",
    post = "r == pow2(n)",

    atoms = {
        # Init: r := 1, i := 0.
        "s@B0": [{"r": "1", "i": "0"}],

        "tau@L0": [
            "r == pow2(i)",
            "0 <= i",
            "i <= n",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Body: r := 2 * r, i := i + 1.
        "s@B1": [{"r": "2 * r", "i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/power_of_two",
    solver_timeout_ms = 1_800_000,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    print(f"wall: {time.monotonic() - t:.1f}s")
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
