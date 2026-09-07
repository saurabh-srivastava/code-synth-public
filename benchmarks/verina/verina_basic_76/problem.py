"""verina_basic_76 — myMin (VERINA-basic port).

Minimum of two integers.  Template is `SB(n=2)` — two guarded
branches in an acyclic block (the 2-arg sibling of
`benchmarks/verina/verina_basic_6_minOfThree.py`).

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_76/):
    signature : myMin (x y : Int) : Int
    precond   : True
    code      : if x < y then x else y
    postcond  : (x ≤ y → result = x) ∧ (x > y → result = y)

Fidelity mapping:
    x, y   : Int -> "int" inputs (no >=0 constraint; VERINA uses Int).
    result : Int -> our output var `result`.
    precond True -> pre = "true".
    postcond     -> post below, transcribed as the logically
                    equivalent disjunctive (implication-free) form:
        (x ≤ y → result = x)  ≡  ((x > y)  or (result == x))
        (x > y  → result = y)  ≡  ((x ≤ y) or (result == y))
      so post = ((x > y) or (result == x)) and
                ((x <= y) or (result == y)).
      This is a bidirectional characterisation of min(x, y):
      when x ≤ y it pins result to x, when x > y it pins result to y.

No auxiliary fold/sum/count function is referenced, so no
uninterpreted function / axiom is needed — this is a pure-Z3
scalar synthesis (trust_axioms = []).

Spec:
    Pre  : true
    Post : (x ≤ y → result = x) ∧ (x > y → result = y)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integers x, y, return the smaller of the two: "
        "x if x <= y, otherwise y."
    ),

    template = SB(n=2),
    inputs   = [Var("x", "int", "input"),
                Var("y", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    # Faithful disjunctive form of VERINA's implication postcond.
    post     = ("((x > y) or (result == x)) and "
                "((x <= y) or (result == y))"),
    atoms = {
        # Branch 0: x <= y, result = x.
        "g@B0.0": ["x <= y"],
        "s@B0.0": [{"result": "x"}],
        # Branch 1: x > y, result = y.
        "g@B0.1": ["x > y"],
        "s@B0.1": [{"result": "y"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_76/lean/SynthLean/Y2Corpus/verina_basic_76",
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
