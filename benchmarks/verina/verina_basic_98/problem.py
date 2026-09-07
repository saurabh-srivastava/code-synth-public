"""verina_basic_98 — Triple (VERINA-basic port).

Compute three times a given integer: `r := x * 3`.  Straight-line
single-branch block `SB(n=1)` — the scalar analogue of
`benchmarks/abs2.py` (`y := x * x`) and `benchmarks/verina/
verina_basic_11_lastDigit.py` (`d := n % 10`).  Pure Z3, no UF,
no Lean.

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_98/):
    signature : Triple (x : Int) : Int
    precond   : True
    code      : x * 3
    postcond  : result / 3 = x ∧ result / 3 * 3 = result

Fidelity mapping:
    x      : Int  -> our "int" input `x` (a true Int — no
                     nonnegativity constraint; the input is signed).
    result : Int  -> our output var `r`.
    precond True  -> pre = "true".
    postcond      -> post below, transcribed clause-for-clause:
        r // 3 == x                    [result / 3 = x]
        and r // 3 * 3 == r            [result / 3 * 3 = result]

    Division-convention note: VERINA's `/` is Lean `Int.div`
    (truncates toward zero); our `//` maps to Z3's integer
    division (Euclidean, rounds toward -inf for negative
    dividends).  The two conventions DIFFER only when the
    dividend is not a multiple of the divisor.  For the reference
    code `r = x * 3` the dividend `r` is ALWAYS a multiple of 3,
    so `r / 3` is exact and both conventions agree (`r/3 = x`,
    `r/3*3 = r`) for every signed `x`, positive or negative.
    Hence the transcription is faithful and the postcond holds
    for exactly the same reason as in the VERINA Lean proof
    (`simp +arith` closes it because `x * 3` is divisible by 3).

    Operator precedence: `r // 3 * 3` parses as `(r // 3) * 3`,
    matching VERINA's `result / 3 * 3 = (result / 3) * 3`.

No auxiliary fold/sum/count/product function is referenced, so no
uninterpreted function / axiom is needed — this is a pure-Z3
scalar synthesis (trust_axioms = []).

Spec:
    Pre  : true
    Post : (r // 3 == x) ∧ (r // 3 * 3 == r)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer x, return three times its value, i.e. "
        "the product of x and 3."
    ),

    template = SB(n=1),
    inputs   = [Var("x", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    pre      = "true",
    post     = "(r // 3 == x) and (r // 3 * 3 == r)",
    atoms = {
        # Single unguarded branch: r := x * 3.
        "s@B0": [
            {"r": "x * 3"},             # published — the reference code
            {"r": "x + 3"},             # distractor — wrong operation
            {"r": "x * 2"},             # distractor — doubles instead
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_98/lean/SynthLean/Y2Corpus/verina_basic_98",
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
