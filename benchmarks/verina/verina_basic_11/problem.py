"""verina_basic_11 — lastDigit (VERINA-basic port).

Extract the last decimal digit of a non-negative integer:
`d := n % 10`.  Straight-line single-branch block `SB(n=1)` —
the scalar analogue of the entry block in `benchmarks/intdiv.py`,
which likewise reasons about `%` / integer division over Z3's
integer theory.

VERINA source of truth
(/private/tmp/verina-data/datasets/verina/verina_basic_11/):
    signature : lastDigit (n : Nat) : Nat
    precond   : True
    code      : n % 10
    postcond  : (0 ≤ result ∧ result < 10) ∧
                (n % 10 - result = 0 ∧ result - n % 10 = 0)

Fidelity mapping:
    n      : Nat  -> our "int" input with the implied `n >= 0`
                    (Nat's nonnegativity carried as the precondition).
    result : Nat  -> our output var `d`.
    precond True  -> pre = "n >= 0".
    postcond      -> post below, transcribed clause-for-clause:
        (d >= 0) and (d < 10)                     [range 0..9]
        and ((n % 10) - d == 0 and d - (n % 10) == 0)
                                                  [d equals n % 10]

    The two subtraction clauses `n % 10 - result = 0` and
    `result - n % 10 = 0` are VERINA's Nat (truncated-subtraction)
    idiom for `result = n % 10`; over our integer IR the pair is
    exactly `d == n % 10`, so the transcription is faithful.  The
    precondition `n >= 0` makes Z3's `%` agree with Nat `%` (both
    land in 0..9), so the range clause and the equality clause hold
    for the same reason they do in the VERINA proof.

No auxiliary fold/sum/count/product function is referenced, so no
uninterpreted function / axiom is needed — this is a pure-Z3 scalar
synthesis.

Spec:
    Pre  : n >= 0
    Post : (d >= 0) ∧ (d < 10) ∧
           ((n % 10) - d == 0 ∧ d - (n % 10) == 0)
"""
from synth import Problem, SB, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-negative integer n, return its last decimal "
        "digit, i.e. n modulo 10 (a value between 0 and 9)."
    ),

    template = SB(n=1),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("d", "int", "output")],
    pre      = "n >= 0",
    post     = (
        "(d >= 0) and (d < 10) and "
        "((n % 10) - d == 0 and d - (n % 10) == 0)"
    ),
    atoms = {
        # Single unguarded branch: d := n % 10.
        "s@B0": [
            {"d": "n % 10"},            # published — the reference code
            {"d": "n"},                 # distractor — out of range for n >= 10
            {"d": "n % 100"},           # distractor — two-digit remainder
        ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_11/lean/SynthLean/Y2Corpus/verina_basic_11",
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
