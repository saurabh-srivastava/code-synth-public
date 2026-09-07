"""verina_basic_58 (double_array_elements) — VERINA-basic port.

Pointwise doubling: B[k] = 2 * A[k] for k in [0, n).  Identical
shape to `array_double` / `verina_basic_13 (cubeElements)`; the
pointwise transform is multiply-by-two.

VERINA source (source of truth):
  signature : double_array_elements (s : Array Int) -> Array Int
  precond   : True   (no preconditions; array may be empty)
  code      : double_array_elements_aux s s 0, where the recursive
              helper sets new_s := s.set! i (2 * s_old[i]!) for each
              i in [0, s.size) and reads the ORIGINAL element via
              s_old (so the result is a fresh doubling, not a
              running compound-double).
  postcond  : (result.size = s.size) ∧
              (∀ i, i < s.size → result[i]! = 2 * s[i]!)

Fidelity mapping:
  - VERINA `s : Array Int`      -> our input array A + length n.
  - VERINA `result : Array Int` -> our output array B.
  - `result.size = s.size`      -> B has length n by construction
                                   (the SB()>>Loop>>SB() shape writes
                                   B[0..n) in place, preserving length).
  - `∀ i < s.size, result[i]! = 2 * s[i]!`
                                -> ForAll k. 0<=k<n => B[k] == 2*A[k].
  - VERINA `True` precond       -> our `n >= 0` (n models s.size, a
                                   Nat, hence implicitly >= 0).

VERINA reads the ORIGINAL element (s_old[i]) when writing index i,
so no read-before-write hazard: our loop reads A[i] (input, never
mutated) and writes B[i], which is the same semantics.

No auxiliary fold/sum/count function is referenced by the postcond,
so this is a PURE Z3 pointwise transform (no UF, no axioms).  The
`2*A[k]` term appears identically on both sides of the inductive
step, so the obligation stays linear.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, an integer array B, and a length "
        "n (with n >= 0), populate B so that B[k] equals 2 * A[k] "
        "for every k in [0, n)."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 0",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == 2*A[k]))",

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "ForAll(lambda k: Implies(0 <= k and k < i, B[k] == 2*A[k]))",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        "s@B1": [{"B": "Update(B, i, 2*A[i])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 2,
    expected_solutions = 2,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_58/lean/SynthLean/Y2Corpus/verina_basic_58",
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
