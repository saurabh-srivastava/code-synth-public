"""factorial — Phase X corpus benchmark (Lean-ish).

Iterative factorial via a multiplicative recurrence UF.  Pure
scalar (no arrays); axiom-heavy.  The obligation has the same
flavor as fib but with multiplication instead of addition —
Z3's quantifier-instantiation often UNKNOWNs on the inductive,
making this a natural Lean-fallthrough candidate.

Algorithm:
    result := 1; i := 1;
    while (i <= n):
        result := result * i;
        i := i + 1;

Spec:
    Pre  : n >= 0
    Post : result == fact(n)

`fact : Int → Int` is uninterpreted with the standard recurrence.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-negative integer n, return n factorial — the "
        "product 1 * 2 * 3 * ... * n.  By convention fact(0) = 1."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("fact", ["int"], "int")],
    axioms = [
        "fact(0) == 1",
        ("ForAll(lambda k: Implies(k >= 0, "
         "fact(k + 1) == (k + 1) * fact(k)))"),
    ],

    pre  = "n >= 0",
    post = "result == fact(n)",

    atoms = {
        # Init: result, i := 1, 1
        "s@B0": [{"result": "1", "i": "1"}],

        "tau@L0": [
            "result == fact(i - 1)",
            "i >= 1",
            "i <= n + 1",
            "n >= 0",
        ],
        "g@L0":   ["i <= n"],
        "phi@L0": ["n + 1 - i"],

        # Body: result := result * i; i := i + 1
        "s@B1": [{"result": "result * i", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    # Observed (2026-05-17, sound default): Lean's generic tactic
    # chain closes 0 of 7 axiom-heavy classes — same shape as fib.
    # Driver-LLM proof sketches (Phase Y.2) will eventually close
    # this; for now opt into lenient.  Captured failure obligations
    # live under `lean/SynthLean/Y2Corpus/` and form the Y.2
    # training data.
    expected_lean_hits = 0,
    # SOUND mode: chain-bundle Lean translator + `.solved.lean`
    # cache for sc#1 (4 τ subsets) and sc#4 (chosen-τ chain-bundle
    # obligation) close the axiom-heavy verifications.  See
    # lean/SynthLean/Y2Corpus/factorial/ + RESEARCH.md §B.
    # Phase Y.2: dump Lean failures to a per-benchmark subdir so
    # we can curate (failed, solved) / (failed, invalid) pairs.
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/factorial",
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
