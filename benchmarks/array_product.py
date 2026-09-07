"""array_product — Phase X corpus benchmark (Lean-ish).

Compute the product of the first n elements of an integer array.
Same shape as `sum_array` but with multiplication — Z3's
quantifier instantiation is typically harder on nonlinear
recurrences, making this a sharper test of Lean fallthrough.

Algorithm:
    p := 1; i := 0;
    while (i < n):
        p := p * A[i];
        i := i + 1;

Spec:
    Pre  : n >= 0
    Post : p == prod(A, n)

`prod : (Int → Int) → Int → Int` with the standard recurrence.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n >= 0), "
        "return the product of A[0], A[1], ..., A[n-1].  The empty "
        "product (n = 0) is 1."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("p", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("prod", ["int[]", "int"], "int")],
    axioms = [
        "prod(A, 0) == 1",
        ("ForAll(lambda k: Implies(k >= 0, "
         "prod(A, k + 1) == prod(A, k) * A[k]))"),
    ],

    pre  = "n >= 0",
    post = "p == prod(A, n)",

    atoms = {
        "s@B0": [{"p": "1", "i": "0"}],

        "tau@L0": [
            "p == prod(A, i)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"p": "p * A[i]", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    # Observed (2026-05-17, sound default): Lean closes 10 of 16
    # axiom-heavy classes — strong dispatch on nonlinear UF, but
    # 6 classes still fail (likely subsets without the right
    # bookkeeping atoms).  Synthesis fails under sound default;
    # opt into lenient.  Captures live under Y2Corpus/.
    expected_lean_hits = 0,
    # SOUND mode: hand-curated `.solved.lean` for sc#1 + sc#4
    # close the axiom-heavy verifications.  See
    # lean/SynthLean/Y2Corpus/array_product/.
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/array_product",
    solver_timeout_ms = 900_000,
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
