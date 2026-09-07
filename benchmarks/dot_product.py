"""dot_product — Phase X corpus benchmark.

Compute the dot product `Σ A[k] * B[k]` for k in 0..n-1.  Like
sum_array but with an element-wise product before reducing.
Uses an UF `dot : (Int → Int) → (Int → Int) → Int → Int`
axiomatized via the standard recurrence.

Spec:
    Pre  : n >= 0
    Post : s == dot(A, B, n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A and B and a length n (with "
        "n >= 0), return the dot product: A[0]*B[0] + A[1]*B[1] "
        "+ ... + A[n-1]*B[n-1]."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("dot", ["int[]", "int[]", "int"], "int")],
    axioms = [
        "dot(A, B, 0) == 0",
        ("ForAll(lambda k: Implies(k >= 0, "
         "dot(A, B, k + 1) == dot(A, B, k) + A[k] * B[k]))"),
    ],

    pre  = "n >= 0",
    post = "s == dot(A, B, n)",

    atoms = {
        "s@B0": [{"s": "0", "i": "0"}],
        "tau@L0": [
            "s == dot(A, B, i)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "s@B1": [{"s": "s + A[i] * B[i]", "i": "i + 1"}],
        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/dot_product",
    solver_timeout_ms = 1_800_000,   # 30 min for axiom-heavy
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
