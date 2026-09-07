"""verina_basic_3 — isDivisibleBy11 (ported from VERINA-basic).

Upstream: VERINA `verina_basic_3` (dafny-synthesis task_id_77).

    signature : isDivisibleBy11(n: Int) -> Bool
    precond   : True
    reference : n % 11 == 0
    postcond  : (result → (∃ k : Int, n = 11 * k)) ∧
                (¬ result → (∀ k : Int, ¬ n = 11 * k))

i.e. `result` is true iff `n` is divisible by 11.

Divisibility encoding (fidelity).  VERINA phrases "n is divisible by
11" as `∃ k : Int, n = 11 * k`.  Over the integers this is
definitionally the divisibility predicate `11 ∣ n`, which is
decidably equivalent to `n % 11 == 0` (Lean: `Int.dvd_iff_emod_eq_zero`
/ `Int.emod_eq_zero_of_dvd`; VERINA's own reference proof closes the
∃/∀ obligations via exactly this bridge).  Z3's integer `%` uses the
same Euclidean convention as Lean's `Int.emod` (result in `[0, 11)`
for the positive modulus, so `n % 11 == 0 ⟺ 11 ∣ n` for every integer
including negatives).  We therefore encode divisibility as
`n % 11 == 0`, which is faithful to VERINA's quantified postcondition
while staying in the quantifier-free fragment Z3 decides directly.
The two VERINA implications collapse to the iff form under this
encoding:

    result → (∃k. n = 11k)   ==   Implies(n % 11 == 0, result == 1)
    ¬result → (∀k. n ≠ 11k)  ==   Implies(not (n % 11 == 0), result == 0)

Bool→int modeling.  Our IR is integer-valued, so the Bool `result`
is modeled as an int with the convention `result == 1` ⇔ true,
`result == 0` ⇔ false.  The two transitions only ever assign 0 or 1,
so `result ∈ {0, 1}` holds in every satisfying solution — no separate
boolean-domain axiom needed.

Template.  Straight-line `SB(n=2)` (an if/else): one branch sets
`result := 1`, the other `result := 0`.  This is the scalar analogue
of `abs.py` / `verina_basic_1`.  The guard candidate lists let the
synthesizer *discover* the reference guard `n % 11 == 0` (and its
complement) against distractors that either violate the post or fail
to cover all of `n`.
"""
from synth import Problem, SB, Var, solve


# The divisibility predicate, reused in the post and the guards.
_DIV = "n % 11 == 0"


PROBLEM = Problem(
    description = (
        "Given an integer n, return true iff n is divisible by 11."
    ),

    template = SB(n=2),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    # Faithful port of VERINA's two-implication postcondition, with the
    # Bool result modeled as int 0/1 and divisibility encoded as `%`.
    post     = (
        f"Implies(({_DIV}), result == 1) and "
        f"Implies(not ({_DIV}), result == 0)"
    ),
    atoms = {
        # Branch 0 — "divisible by 11" ⇒ result := 1.
        "g@B0.0": [
            _DIV,                    # the reference implementation
            "n % 11 > 0",            # distractor — unsound (misses)
            "n > 0",                 # distractor — unsound cover
        ],
        "s@B0.0": [{"result": "1"}],

        # Branch 1 — "not divisible by 11" ⇒ result := 0.
        "g@B0.1": [
            "n % 11 != 0",           # complement of the reference
            _DIV,                    # distractor — fails to cover
            "n < 0",                 # distractor — unsound cover
        ],
        "s@B0.1": [{"result": "0"}],
    },
    max_solutions = 4,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_3/lean/SynthLean/Y2Corpus/verina_basic_3",
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
