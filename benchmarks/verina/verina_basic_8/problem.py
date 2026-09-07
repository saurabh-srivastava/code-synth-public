"""verina_basic_8 (myMin) — VERINA-basic port.

Minimum of two integers.  VERINA reference code is
`if a <= b then a else b`.  Straight-line two-way conditional,
so the template is `SB(n=2)`.  Pure Z3 — no UF, no Lean.

VERINA spec (from datasets/verina/verina_basic_8/task.lean,
between the @start/@end markers):
    precond  : True
    code     : if a <= b then a else b
    postcond : (result ≤ a ∧ result ≤ b) ∧ (result = a ∨ result = b)

Port / fidelity mapping:
    Pre  : true                       (VERINA precond is True)
    Post : (m <= a) and (m <= b) and ((m == a) or (m == b))
           — VERINA output var `result` -> our output var `m`.
             Int params stay int (no Nat coercion needed).
    This is a faithful 1:1 transcription of VERINA's postcond:
    both conjuncts (lower-bound-of-both, and equal-to-one-of)
    are preserved verbatim over the renamed output variable.

Two branches mirror the reference `if a <= b`:
    B0: a <= b  ->  m := a
    B1: b <= a  ->  m := b   (the "else"; guards overlap at a==b
                              but jointly cover all of Int)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integers a, b, return the minimum — the value "
        "less than or equal to both, and equal to one of them."
    ),

    template = SB(n=2),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    pre      = "true",
    # VERINA postcond, verbatim over output var m.
    post     = "(m <= a) and (m <= b) and ((m == a) or (m == b))",
    atoms = {
        # Branch 0: a is the min (reference `if a <= b then a`).
        "g@B0.0": ["a <= b"],
        "s@B0.0": [{"m": "a"}],
        # Branch 1: b is the min (the `else b`).
        "g@B0.1": ["b <= a"],
        "s@B0.1": [{"m": "b"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_8/lean/SynthLean/Y2Corpus/verina_basic_8",
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
