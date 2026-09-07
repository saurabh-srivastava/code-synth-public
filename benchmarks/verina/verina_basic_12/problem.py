"""verina_basic_12 — cubeSurfaceArea (scalar, pure Z3).

Ported from VERINA-basic task `verina_basic_12`
(/private/tmp/verina-data/datasets/verina/verina_basic_12/).

VERINA spec (source of truth):
    signature : cubeSurfaceArea (size : Nat) : Nat
    precond   : True
    code      : 6 * size * size
    postcond  : result - 6 * size * size = 0
                ∧ 6 * size * size - result = 0

Fidelity mapping
----------------
- `size : Nat`  ->  `size : int` with the implied `size >= 0`
  encoded in our `pre` (Nat inputs are non-negative).
- `result : Nat`  ->  `result : int` output.  Since the reference
  code returns `6*size*size >= 0`, the int model stays inside the
  Nat range, so no truncation subtlety is lost.
- VERINA's postcond is Nat truncated subtraction: for Nat a, b,
  `a - b = 0 ∧ b - a = 0` holds iff `a == b`.  Under our int model
  with `size >= 0` (hence both sides non-negative), this is exactly
  the equality `result == 6 * size * size`.  So our `post`
  faithfully captures VERINA's postcond.

Shape
-----
Straight-line acyclic block `SB(n=1)` — an unconditional single
assignment.  Same template as `benchmarks/abs2.py` (the closest
reference: pure scalar, single store, no branching, no loop).
Nonlinear `size*size` is handled directly by Z3's NIA, exactly as
abs2's `x*x`.  No uninterpreted functions, no Lean dispatch.

Spec:
    Pre  : size >= 0
    Post : result == 6 * size * size
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given the edge length `size` of a cube, return its surface "
        "area, 6 * size * size."
    ),

    template = SB(n=1),
    inputs   = [Var("size", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "size >= 0",                       # Nat -> int nonneg
    post     = "result == 6 * size * size",       # VERINA postcond (see docstring)
    atoms = {
        "s@B0": [
            {"result": "6 * size * size"},        # published — correct
            {"result": "6 * size"},               # distractor (perimeter-ish)
            {"result": "size * size"},            # distractor (one face)
        ],
    },
    max_solutions = 3,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_12/lean/SynthLean/Y2Corpus/verina_basic_12",
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
