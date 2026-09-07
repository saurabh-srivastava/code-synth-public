"""verina_basic_6 — minOfThree (VERINA-basic port).

Minimum of three integers.  Template is `SB(n=3)` — three
guarded branches in an acyclic block (the min-dual of
`benchmarks/max3.py`).

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_6/):
    signature : minOfThree (a b c : Int) : Int
    precond   : True
    code      : if a<=b && a<=c then a
                else if b<=a && b<=c then b
                else c
    postcond  : (result <= a ∧ result <= b ∧ result <= c) ∧
                (result = a ∨ result = b ∨ result = c)

Fidelity mapping:
    a, b, c : Int -> "int" inputs (no >=0 constraint; VERINA uses Int).
    result  : Int -> our output var `m`.
    precond True   -> pre = "true".
    postcond       -> post below, transcribed verbatim:
        (m <= a) and (m <= b) and (m <= c)   [result <= each input]
        and ((m == a) or (m == b) or (m == c)) [result is one of them]

No auxiliary fold/sum/count function is referenced, so no
uninterpreted function / axiom is needed — this is a pure-Z3
scalar synthesis.

Spec:
    Pre  : true
    Post : (m <= a) ∧ (m <= b) ∧ (m <= c) ∧
           ((m == a) ∨ (m == b) ∨ (m == c))
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given three integers a, b, c, return the minimum of the "
        "three."
    ),

    template = SB(n=3),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input"),
                Var("c", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    pre      = "true",
    post     = ("(m <= a) and (m <= b) and (m <= c) and "
                "((m == a) or (m == b) or (m == c))"),
    atoms = {
        # Branch 0: a is the min.
        "g@B0.0": ["(a <= b) and (a <= c)"],
        "s@B0.0": [{"m": "a"}],
        # Branch 1: b is the min.
        "g@B0.1": ["(b <= a) and (b <= c)"],
        "s@B0.1": [{"m": "b"}],
        # Branch 2: c is the min.
        "g@B0.2": ["(c <= a) and (c <= b)"],
        "s@B0.2": [{"m": "c"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_6/lean/SynthLean/Y2Corpus/verina_basic_6",
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
