"""verina_basic_5 — multiply (VERINA-basic port).

Multiply two integers and return the product.  Template is
`SB(n=1)` — a single straight-line assignment block (the
scalar-return dual of `benchmarks/abs2.py`).

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_5/):
    signature : multiply (a b : Int) : Int
    precond   : True                       (no preconditions)
    code      : a * b
    postcond  : result - a * b = 0 ∧ a * b - result = 0

Fidelity mapping:
    a, b   : Int -> "int" inputs (no >=0 constraint; VERINA uses Int).
    result : Int -> our output var `p`.
    precond True -> pre = "true".
    postcond     -> post below, transcribed verbatim as the
        two-clause conjunction:
            (p - a*b == 0) and (a*b - p == 0)
        which is logically exactly `p == a * b` (the intended
        "result is the product").  We keep the literal two-clause
        form to mirror VERINA's postcond character-for-character.

No auxiliary fold/sum/count/product function is referenced (the
product is a primitive `a * b`, not a recursive fold), so no
uninterpreted function / axiom is needed — this is a pure-Z3
NIA scalar synthesis.

Spec:
    Pre  : true
    Post : (p - a*b == 0) ∧ (a*b - p == 0)   i.e. p == a * b
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integers a and b, return their product a * b."
    ),

    template = SB(n=1),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input")],
    outputs  = [Var("p", "int", "output")],
    pre      = "true",
    post     = "(p - a*b == 0) and (a*b - p == 0)",
    atoms = {
        # Single straight-line branch: p := a * b.
        "s@B0": [{"p": "a * b"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_5/lean/SynthLean/Y2Corpus/verina_basic_5",
    wedge_threshold = 200,
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
