"""Fibonacci — Phase 3.D benchmark, uninterpreted-function axioms.

Iterative Fibonacci via a counter loop:

    a, b, i := 0, 1, 0;
    while (i < n) {
        a, b, i := b, a + b, i + 1;
    }
    f := a;

The meaning of `fib` is supplied as three axioms over an uninterpreted
function symbol; the synthesizer discovers the invariant that ties the
program state to `fib`.

Spec:
    Pre  : n >= 0
    Post : f == fib(n)

Expected invariant: `a == fib(i)  ∧  b == fib(i+1)  ∧  0 <= i  ∧  i <= n`.

The atom set is intentionally minimal (one atom per non-τ hole) — the
naive CEGIS loop in `synth/solver.py` is O(search-space) in the worst
case, so adding distractors quickly blows up the runtime.  See
CLAUDE.md lesson #8: scaling Phase 3.D to realistic predicate spaces
needs PLDI'09's predicate-abstraction reduction with attribute-class
blocking (deferred to a follow-on phase).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("f", "int", "output")],
    locals   = [Var("a", "int", "local"),
                Var("b", "int", "local"),
                Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "f == fib(n)",

    uninterpreted = [("fib", ["int"], "int")],
    axioms = [
        "fib(0) == 0",
        "fib(1) == 1",
        "ForAll(lambda k: Implies(k >= 0, fib(k + 2) == fib(k + 1) + fib(k)))",
    ],

    atoms = {
        "tau@L0": [
            "a == fib(i)",
            "b == fib(i + 1)",
            "0 <= i",
            "i <= n",
        ],
        "g@L0":  ["i < n"],
        "phi@L0": ["n - i"],
        "s@B0":  [{"a": "0", "b": "1", "i": "0"}],
        "s@B1":  [{"a": "b", "b": "a + b", "i": "i + 1"}],
        "s@B2":  [{"f": "a"}],
    },
    max_solutions = 3,
    # Sound-mode synthesis returns 1 solution (the canonical 4-atom
    # τ).  Under the prior lenient mode, this was 3 — the extra two
    # were unsound τ subsets accepted by lenient deferral that
    # sound mode + chain-bundle Lean translator now correctly
    # rejects.  See `EXPERIENCE_REPORT.md` CS-3.
    expected_solutions = 1,
    expected_lean_hits = 0,
    # SOUND mode: hand-curated `.solved.lean` for sc#1 (loop
    # inductive, recurrence application) and sc#4 (chain-bundle
    # post, `i = n` substitution) close the axiom-heavy
    # verifications.  See lean/SynthLean/Y2Corpus/fib/.
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/fib",
    solver_timeout_ms = 900_000,
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
