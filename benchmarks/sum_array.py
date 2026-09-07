"""sum_array — Ring 2 compressor-style benchmark.

Compute the sum of an integer array via a recursive UF spec.
"Compression" in the sense that the array reduces to a scalar;
the load-bearing feature is the **recursive UF over array reads**,
which exercises Lean's structural-induction strength.

    s := 0
    i := 0
    while (i < n):
        s := s + A[i]
        i := i + 1
    // post: s == sum(A, n)

The spec uses an uninterpreted function `sum : (Int → Int) → Int
→ Int` with axioms:

    sum(A, 0) = 0
    sum(A, n+1) = sum(A, n) + A[n]   for n ≥ 0

Like Fibonacci (the slow-suite benchmark), this is axiom-heavy:
Z3 has to do E-matching on `sum` repeatedly to discharge the
loop inductive (`s == sum(A, i)` preserved across `s := s + A[i];
i := i + 1`).  Where this benchmark differs from fib is that the
recurrence reads from an ARRAY, not just scalars — Lean's tactics
(rewrite via the recurrence axiom) handle it cleanly; Z3's
quantifier instantiation tends to struggle.

Spec:
    Pre  : n ≥ 0
    Post : s == sum(A, n)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("s", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [
        ("sum", ["int[]", "int"], "int"),
    ],
    axioms = [
        # Base.
        "sum(A, 0) == 0",
        # Recurrence.
        ("ForAll(lambda k: Implies(k >= 0, "
         "sum(A, k + 1) == sum(A, k) + A[k]))"),
    ],

    pre  = "n >= 0",
    post = "s == sum(A, n)",

    atoms = {
        # s, i := 0, 0
        "s@B0": [{"s": "0", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "s == sum(A, i)",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Loop body: s := s + A[i]; i := i + 1.
        "s@B1": [{"s": "s + A[i]", "i": "i + 1"}],
    },

    max_solutions = 1,
    expected_solutions = 1,
    # Lean dispatches 2 of ~7 attribute-class UNKNOWNs Z3 hits on
    # sum_array's inductive (`s == sum(A, i)` after the body
    # `s, i := s + A[i], i + 1`).  Bumping this signals a tactic-
    # chain regression if it drops below 2 in the future.  Improvements
    # are also caught — bump the expected when more classes start
    # closing.
    expected_lean_hits = 2,
    solver_timeout_ms = 600_000,   # 10 min

    # SOUND mode: hand-curated `.solved.lean` for sc#1 (loop
    # inductive, recurrence application) and sc#4 (chain-bundle
    # post, `i = n` substitution) close the axiom-heavy
    # verifications.  See lean/SynthLean/Y2Corpus/sum_array/.
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/sum_array",
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    elapsed = time.monotonic() - t
    print(f"wall: {elapsed:.1f}s")
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
