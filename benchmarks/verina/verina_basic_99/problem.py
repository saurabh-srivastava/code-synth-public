"""verina_basic_99 — Triple2 (scalar, pure Z3).

Ported from VERINA-basic task `verina_basic_99`
(/private/tmp/verina-data/datasets/verina/verina_basic_99/).

VERINA spec (source of truth):
    signature : Triple (x : Int) : Int
    precond   : True
    code      : if x < 18 then
                  let a := 2 * x; let b := 4 * x; (a + b) / 2
                else
                  let y := 2 * x; x + y
    postcond  : result / 3 = x ∧ result / 3 * 3 = result

Fidelity mapping
----------------
- `x : Int`  ->  `x : int` input.  No precondition (`True`), so our
  `pre = "true"`.
- `result : Int`  ->  `result : int` output.
- VERINA's postcond is `result / 3 = x ∧ result / 3 * 3 = result`
  over Lean `Int` division (`/`).  Our expression language maps
  Python `//` to Z3 integer division and to Lean `/` (see
  `synth/expr.py:FloorDiv` and `synth/lean_backend/translate.py`),
  so `post` is a byte-faithful transcription of VERINA's postcond,
  same operator and same left-associative grouping
  (`result / 3 * 3` == `(result / 3) * 3`).
- The reference code branches on `x < 18`, but BOTH branches compute
  `3 * x` (branch 1: `(2x + 4x)/2 = 6x/2 = 3x`; branch 2:
  `x + 2x = 3x`).  The postcond does not require branching, so the
  synthesizer discharges it with the single unconditional store
  `result := 3 * x`.  For `result = 3*x` the postcond holds under
  any integer-division rounding convention because 3 divides 3*x
  exactly (`(3x)/3 = x`, `x*3 = 3x = result`).  Z3 confirms
  validity directly (checked: negation is UNSAT).

Shape
-----
Straight-line acyclic block `SB(n=1)` — one unconditional
assignment.  Same template as `benchmarks/abs2.py` /
`benchmarks/verina/verina_basic_12_cubeSurfaceArea.py` (pure scalar,
single store, no branching, no loop).  Integer division by the
constant 3 is handled directly by Z3's LIA (div-by-numeral is a
native rewrite).  No uninterpreted functions, no Lean dispatch.

Spec:
    Pre  : true
    Post : result / 3 == x  and  result / 3 * 3 == result
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x, return three times x (3 * x)."
    ),

    template = SB(n=1),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    # VERINA postcond, byte-faithful (`//` -> Z3 int div / Lean `/`).
    post     = "result // 3 == x and result // 3 * 3 == result",
    atoms = {
        "s@B0": [
            {"result": "3 * x"},              # published — correct (= 3x)
            {"result": "2 * x"},              # distractor (= 2x, wrong)
            {"result": "x + x"},              # distractor (= 2x, wrong)
        ],
    },
    max_solutions = 3,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_99/lean/SynthLean/Y2Corpus/verina_basic_99",
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
