"""verina_basic_7 — sumOfSquaresOfFirstNOddNumbers (scalar, pure Z3).

Ported from VERINA-basic task `verina_basic_7`
(/private/tmp/verina-data/datasets/verina/verina_basic_7/).

VERINA spec (source of truth)
-----------------------------
    signature : sumOfSquaresOfFirstNOddNumbers (n : Nat) : Nat
    precond   : True
    code      : let rec loop (k sum : Nat) : Nat :=
                  if k = 0 then sum
                  else loop (k - 1) (sum + (2*k - 1) * (2*k - 1))
                loop n 0
    postcond  : result - (n * (2*n - 1) * (2*n + 1)) / 3 = 0
                ∧ (n * (2*n - 1) * (2*n + 1)) / 3 - result = 0

The reference `code` is a count-down accumulator that sums
`(2k-1)^2` for k = n, n-1, ..., 1 — i.e. the sum of the squares of
the first n odd naturals.  The postcond, however, is the SPEC, and
it is the *closed form* of that sum:

    sum_{j=1}^{n} (2j-1)^2  =  n * (2n-1) * (2n+1) / 3.

(Check: n=1 -> 1*1*3/3 = 1 = 1^2; n=2 -> 2*3*5/3 = 10 = 1+9;
n=3 -> 3*5*7/3 = 35 = 1+9+25.)  So a straight-line program that
returns the closed form satisfies VERINA's postcond directly — the
same porting move used by the sibling closed-form scalar task
`benchmarks/verina/verina_basic_12_cubeSurfaceArea.py`.

Fidelity mapping
----------------
- `n : Nat`  ->  `n : int` with the implied `n >= 0` encoded in
  our `pre` (Nat inputs are non-negative).
- `result : Nat`  ->  `result : int` output.  For n >= 0 the
  formula value is non-negative (product of n, 2n-1, 2n+1 — see the
  n=0 note below), so the int model stays inside the Nat range; no
  truncation is lost.
- Division: VERINA's `/` is Nat floor division; our `/` maps to Z3
  Int division (`synth/expr.py` — both `/` and `//` become Z3 `div`,
  which is floor division for non-negative operands).  The product
  `n*(2n-1)*(2n+1)` is ALWAYS exactly divisible by 3 (among the three
  consecutive integers 2n-1, 2n, 2n+1 one is a multiple of 3; if it
  is 2n then 3 | n), so floor division is exact and Z3's `div` agrees
  with Nat's on every n >= 0.
- n = 0 Nat-truncation edge: in Nat, `2*0 - 1 = 0` (truncated), so
  VERINA's formula is `0 * 0 * 1 / 3 = 0`.  In our int model
  `2*0 - 1 = -1`, giving `0 * (-1) * 1 / 3 = 0 / 3 = 0`.  Both are 0
  because the leading `n` factor is 0, so the int model agrees with
  Nat at n=0 too.  For n >= 1, `2n-1 >= 1`, so Nat and int
  subtraction coincide and the products match exactly.
- VERINA's postcond is Nat truncated subtraction:
  `a - b = 0 ∧ b - a = 0` holds iff `a == b`.  Under our int model
  (both sides non-negative for n >= 0) this is exactly the equality
  `result == (n*(2n-1)*(2n+1))/3`.  So our `post` faithfully
  captures VERINA's postcond.

Shape
-----
Straight-line acyclic block `SB(n=1)` — one unconditional
assignment.  Same template + porting recipe as
`benchmarks/verina/verina_basic_12_cubeSurfaceArea.py` (the closest
reference: pure scalar, single store, closed-form Nat->Nat).  The
cubic-with-division expression is handled directly by Z3's NIA + int
`div`.  No uninterpreted functions, no axioms, no Lean dispatch.

Spec:
    Pre  : n >= 0
    Post : result == (n * (2*n - 1) * (2*n + 1)) / 3
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given a natural number n, return the sum of the squares of "
        "the first n odd natural numbers, which equals the closed "
        "form n * (2n - 1) * (2n + 1) / 3."
    ),

    template = SB(n=1),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "n >= 0",                                     # Nat -> int nonneg
    post     = "result == (n * (2*n - 1) * (2*n + 1)) / 3",  # VERINA postcond (see docstring)
    atoms = {
        "s@B0": [
            {"result": "(n * (2*n - 1) * (2*n + 1)) / 3"},   # published — correct closed form
            {"result": "n * n"},                             # distractor: sum (not sum of squares) of first n odds
            {"result": "n * (2*n - 1) * (2*n + 1)"},         # distractor: forgot the / 3
            {"result": "(n * (2*n + 1) * (2*n + 1)) / 3"},   # distractor: wrong middle factor
        ],
    },
    max_solutions = 4,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_7/lean/SynthLean/Y2Corpus/verina_basic_7",
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
