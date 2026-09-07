"""gcd — Phase X corpus benchmark.

Euclidean algorithm via repeated subtraction: while a ≠ b,
replace the larger by their difference.  Terminates at the GCD.
Uses an UF `gcd_uf` axiomatized so that subtraction preserves
the GCD.

Spec:
    Pre  : a > 0 ∧ b > 0
    Post : g == gcd_uf(a₀, b₀)         (initial values of a, b)

We use ghost copies `a0`, `b0` of the initial inputs so the
post can reference them.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two positive integers a and b, compute their "
        "greatest common divisor using Euclidean subtraction: "
        "while a ≠ b, replace the larger with their difference."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("a0", "int", "input"),
                Var("b0", "int", "input")],
    outputs  = [Var("g", "int", "output")],
    locals   = [Var("a", "int", "local"),
                Var("b", "int", "local")],

    uninterpreted = [("gcd_uf", ["int", "int"], "int")],
    axioms = [
        # GCD is symmetric.
        "ForAll(lambda x, y: Implies(x > 0 and y > 0, "
        "gcd_uf(x, y) == gcd_uf(y, x)))",
        # Idempotent on equal arguments.
        "ForAll(lambda x: Implies(x > 0, gcd_uf(x, x) == x))",
        # Subtraction preserves the gcd: gcd(x, y) = gcd(x - y, y)
        # when x > y > 0.
        ("ForAll(lambda x, y: Implies(x > y and y > 0, "
         "gcd_uf(x, y) == gcd_uf(x - y, y)))"),
    ],

    pre  = "(a0 > 0) and (b0 > 0)",
    post = "g == gcd_uf(a0, b0)",

    atoms = {
        # Init: a := a0, b := b0.
        "s@B0": [{"a": "a0", "b": "b0"}],

        "tau@L0": [
            "a > 0",
            "b > 0",
            "gcd_uf(a, b) == gcd_uf(a0, b0)",
        ],
        "g@L0":   ["a != b"],
        "phi@L0": ["a + b"],

        # Branch 0: a > b → a := a - b.
        "g@B1.0": ["a > b"],
        "s@B1.0": [{"a": "a - b"}],
        # Branch 1: a < b → b := b - a.
        "g@B1.1": ["a < b"],
        "s@B1.1": [{"b": "b - a"}],

        # Final: g := a.  (a = b at exit, so g = a = b = gcd.)
        "s@B2": [{"g": "a"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/gcd",
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
