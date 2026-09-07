"""verina_basic_50 (Abs) — integer absolute value.

Ported from VERINA-basic task `verina_basic_50`
(upstream: Clover / Clover_abs).

VERINA spec (source of truth,
/private/tmp/verina-data/datasets/verina/verina_basic_50/task.lean):

    signature : Abs (x : Int) : Int
    precond   : True                                    (any integer)
    code      : if x < 0 then -x else x
    postcond  : (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)

Shape: scalar, straight-line SB(n=2) (one conditional block, two
guarded branches).  No loop, no auxiliary fold/sum function, so no
uninterpreted function is needed — this closes in pure Z3.

Mapping to our IR:
  - VERINA `x : Int`        -> Var("x", "int", "input").
  - VERINA `result : Int`   -> Var("result", "int", "output").
  - VERINA precond `True`   -> pre = "true".
  - VERINA postcond
        (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)
    is ported VERBATIM as a conjunction of two implications:
        Implies(x >= 0, result == x) and Implies(x < 0, x + result == 0)
    (note: the second conjunct says result == -x on the negative
    branch, exactly VERINA's `x + result = 0`; we do NOT weaken it to
    the classic `result >= 0 and (result == x or result == -x)` form
    used by benchmarks/abs.py — we keep VERINA's directional equalities
    so the fidelity claim is exact.)

Fidelity: our (pre, post) are a literal transcription of VERINA's
`Abs_precond` / `Abs_postcond`.  No quantifiers, no auxiliary
functions, no abstraction — the correspondence is 1:1.

Template `SB(n=2)` recovers the reference body:
    if (x < 0) result := -x;
    else       result :=  x;

Guards are pinned to the reference branch conditions (x<0 / x>=0) so
the search yields exactly the reference program; the transition atoms
carry distractors so the postcond genuinely discriminates the correct
assignment on each branch.
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x, return its absolute value: x if x >= 0, "
        "else -x (VERINA verina_basic_50 / Clover_abs)."
    ),

    template = SB(n=2),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    post     = (
        "Implies(x >= 0, result == x) and "
        "Implies(x < 0, x + result == 0)"
    ),
    atoms = {
        # Branch 0 guard: x negative.
        "g@B0.0": ["x < 0"],
        # Branch 0 transition: result := -x  (distractors rejected by post).
        "s@B0.0": [
            {"result": "0 - x"},   # published — correct on the x<0 branch
            {"result": "x"},       # wrong: leaves negative value
            {"result": "0"},       # wrong: collapses to 0
        ],
        # Branch 1 guard: the "else" — x non-negative.
        "g@B0.1": ["x >= 0"],
        # Branch 1 transition: result := x  (distractors rejected by post).
        "s@B0.1": [
            {"result": "x"},       # published — correct on the x>=0 branch
            {"result": "0 - x"},   # wrong: negates a non-negative value
            {"result": "0"},       # wrong: collapses to 0
        ],
    },
    max_solutions = 5,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_50/lean/SynthLean/Y2Corpus/verina_basic_50",
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
