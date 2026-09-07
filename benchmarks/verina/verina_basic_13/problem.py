"""verina_basic_13 (cubeElements) — VERINA-basic port.

Pointwise cube: B[k] = A[k] * A[k] * A[k] for k in [0, n).  Same
shape as `array_double` / `negate_array`, but the pointwise
transform is the cube of each element.

VERINA source (source of truth):
  signature : cubeElements (a : Array Int) -> Array Int
  precond   : True   (no preconditions; array may be empty)
  code      : a.map (fun x => x * x * x)
  postcond  : (result.size = a.size) ∧
              (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)

Fidelity mapping:
  - VERINA `a : Array Int`      -> our input array A + length n.
  - VERINA `result : Array Int` -> our output array B.
  - `result.size = a.size`      -> B has length n by construction
                                   (the SB()>>Loop>>SB() shape writes
                                   B[0..n) in place, preserving length).
  - `∀ i < a.size, result[i]! = a[i]!^3`
                                -> ForAll k. 0<=k<n => B[k]==A[k]*A[k]*A[k].
  - VERINA `True` precond       -> our `n >= 0` (n models a.size, a Nat,
                                   hence implicitly >= 0).

No auxiliary fold/sum/count function is referenced by the postcond,
so this is a PURE Z3 pointwise transform (no UF, no axioms).  The
cubic term A[k]*A[k]*A[k] appears identically on both sides of the
inductive step, so it is treated congruently — no nonlinear search.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, an integer array B, and a length "
        "n (with n >= 0), populate B so that B[k] equals the cube "
        "A[k] * A[k] * A[k] for every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]*A[k]*A[k]))",

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "ForAll(lambda k: Implies(0 <= k and k < i, B[k] == A[k]*A[k]*A[k]))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"B": "Update(B, i, A[i]*A[i]*A[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 2,
    expected_solutions = 2,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_13/lean/SynthLean/Y2Corpus/verina_basic_13",
    wedge_threshold = 200,
    solver_timeout_ms = 120_000,
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
