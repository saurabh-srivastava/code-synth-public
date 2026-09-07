"""verina_basic_83 (concat) — VERINA-basic port.

Concatenate two integer arrays: produce C such that the first
`na` elements equal A and the next `nb` elements equal B.  This is
the classic single-loop concat with a branched value expression —
matching VERINA's reference code exactly:

    let n := a.size + b.size
    loop i in [0, n):
        c[i] := if i < a.size then a[i] else b[i - a.size]

Shape: array -> array.  PURE Z3 — concat is a copy/permutation
into a fresh output, no element accumulation, so no uninterpreted
function or axioms are required.  A single quantified prefix
invariant (split into an A-part and a B-part) discharges both
postcondition conjuncts.

────────────────────────────────────────────────────────────────
VERINA correspondence (source of truth:
/private/tmp/verina-data/datasets/verina/verina_basic_83)
────────────────────────────────────────────────────────────────
Signature (VERINA):
    concat (a : Array Int) (b : Array Int) : Array Int

Precondition (VERINA):
    True                    -- no constraints

Postcondition (VERINA):
    result.size = a.size + b.size
      ∧ (∀ k, k < a.size → result[k]!        = a[k]!)
      ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)

Our mapping:
    a          -> input array A,   a.size -> int na (>= 0 implied)
    b          -> input array B,   b.size -> int nb (>= 0 implied)
    result     -> output array C   (passed in as a scratch array and
                                    fully overwritten on [0, na+nb))

    pre  : na >= 0 and nb >= 0
    post : ForAll k. 0 <= k < na          => C[k]      == A[k]      (conjunct 2)
         ∧ ForAll k. 0 <= k < nb          => C[k + na] == B[k]      (conjunct 3)

FIDELITY: VERINA's Nat sizes become non-negative ints (na, nb >= 0
in pre).  VERINA conjunct 1 (`result.size = a.size + b.size`) is a
LENGTH claim; our IR models arrays as unbounded maps with the
length tracked separately, so length equality is structural (the
output is built over exactly [0, na+nb)) rather than a proof
obligation — it is not restated as a Z3 conjunct.  Conjuncts 2 and
3 (the element-wise value claims, which are the algorithmic content)
are captured verbatim over our output var C.  The `∀ k < b.size`
Nat quantifier in VERINA implicitly ranges over k >= 0; we make the
`0 <= k` lower bound explicit.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given two integer arrays A (length na) and B (length nb), "
        "both non-negative, populate output array C of length na+nb so "
        "that C[0..na) equals A and C[na..na+nb) equals B."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("C", "int[]", "input"),
                Var("na", "int", "input"),
                Var("nb", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "na >= 0 and nb >= 0",
    post     = (
        "ForAll(lambda k: Implies(0 <= k and k < na, C[k] == A[k])) and "
        "ForAll(lambda k: Implies(0 <= k and k < nb, C[k + na] == B[k]))"
    ),

    atoms = {
        # Init: i := 0.
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= na + nb",
            "na >= 0",
            "nb >= 0",
            # A-part prefix: everything below min(i, na) matches A.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < na and k < i, C[k] == A[k]))"),
            # B-part prefix: every B index whose target (k + na) is
            # already written matches B.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < nb and k + na < i, C[k + na] == B[k]))"),
        ],
        "g@L0":   ["i < na + nb"],
        "phi@L0": ["na + nb - i"],

        # Body: C[i] := (i < na ? A[i] : B[i - na]); i := i + 1.
        "s@B1": [{"C": "Update(C, i, A[i] if i < na else B[i - na])",
                  "i": "i + 1"}],

        # Final: no-op.
        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 120_000,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_83/lean/SynthLean/Y2Corpus/verina_basic_83",
    wedge_threshold = 200,
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
