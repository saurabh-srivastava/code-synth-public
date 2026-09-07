"""verina_basic_100 (Triple3) — ported VERINA-basic scalar task.

Source: VERINA verina_basic_100, upstream Clover `triple3`.
Signature: `Triple(x : Int) : Int`.

VERINA spec (verbatim, from task.lean between the @start/@end
markers):

    precond  : True
    code     : if x = 0 then 0 else (let y := 2 * x; x + y)
    postcond : result / 3 = x ∧ result / 3 * 3 = result

The function returns three times its integer input.  Both code
branches evaluate to `3 * x` (the `x = 0` special-case yields
`0 = 3 * 0`; the else-branch yields `x + 2*x = 3*x`).

Fidelity mapping (VERINA -> this Problem):
  - precond `True`                        -> pre  = "true".
  - postcond `result / 3 = x ∧            -> post = "(r // 3 == x) and
              result / 3 * 3 = result`             (r // 3 * 3 == r)".
    `/` here is integer division.  We reproduce it verbatim with
    `//` (which the parser lowers to Z3's integer `/` on Int; see
    synth/expr.py:109).  For the reference output `r = 3*x` the
    divisions are exact, so BOTH conjuncts hold and the pair is
    logically equivalent to `r == 3*x` — a faithful, literal port
    of VERINA's postcondition rather than a hand-simplified one.
  - return type `Int`                     -> output Var `r : int`.
  - param `x : Int`                       -> input  Var `x : int`.

Template: SB(n=1) — a single straight-line block emitting the
return value.  Both VERINA branches collapse to `r := 3*x`; the
`x = 0` case is subsumed (there is no precondition to model and
`3*0 = 0`), so a single unconditional transition captures the
whole function.

Pure Z3 — no uninterpreted functions, no axioms, no Lean.
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x, return 3 * x (VERINA verina_basic_100, "
        "Triple / Clover triple3)."
    ),

    template = SB(n=1),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    pre      = "true",
    # Verbatim port of VERINA's postcond `result / 3 = x ∧
    # result / 3 * 3 = result` over our output var `r`.
    post     = "(r // 3 == x) and (r // 3 * 3 == r)",
    atoms = {
        "s@B0": [
            {"r": "3 * x"},        # published — returns 3*x
            {"r": "x"},            # distractor — 1*x
            {"r": "2 * x"},        # distractor — 2*x
            {"r": "3 * x + 1"},    # distractor — off by one
        ],
    },
    max_solutions = 4,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_100/lean/SynthLean/Y2Corpus/verina_basic_100",
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
