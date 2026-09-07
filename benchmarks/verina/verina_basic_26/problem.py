"""verina_basic_26_isEven — VERINA-basic port (isEven).

Ported from VERINA task `verina_basic_26` (isEven; upstream
dafny-synthesis task_id_600).  Determine whether an integer is even.

VERINA signature (source of truth):
    isEven(n : Int) -> Bool
VERINA precondition (task.lean, between @start/@end precond):
    True
VERINA reference code:
    n % 2 == 0
VERINA postcondition (task.lean, between @start/@end postcond):
    (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)

Framework encoding
------------------
    Pre  : true
    Post : Implies(result == 1, n % 2 == 0) and
           Implies(result == 0, n % 2 != 0)

NAMING MAP (VERINA -> ours):
    VERINA `n`      (Int, scalar)   -> our `n`      (int, the input)
    VERINA `result` (Bool)          -> our `result` (int, 0/1)

Bool->int modeling.  Our IR is integer-valued, so the Bool `result`
is modeled as an int with the convention `result == 1` ⇔ true,
`result == 0` ⇔ false.  The two transitions only ever assign 0 or 1,
so `result ∈ {0, 1}` holds in every satisfying solution — no separate
boolean-domain axiom needed.  This is the same Bool->int coding used
by the sibling predicate benchmark `verina_basic_3_isDivisibleBy11`.

SPEC-FIDELITY NOTE
------------------
The post is a LITERAL transcription of VERINA's postcondition under the
Bool->{0,1} coding: VERINA's `result → n % 2 = 0` is our
`Implies(result == 1, n % 2 == 0)`, and VERINA's `¬ result → n % 2 ≠ 0`
is our `Implies(result == 0, n % 2 != 0)`.  Because `result ∈ {0, 1}`
is total, these two forward implications are together equivalent to the
biconditional `result == 1 ⇔ (n % 2 == 0)`.  VERINA's `n % 2` is our
`n % 2` verbatim; Z3's integer `%` uses the same Euclidean convention
as Lean's `Int.emod` (result in `[0, 2)`), and divisibility-by-2 is
sign-independent, so `n % 2 == 0 ⟺ n even` holds identically in both
Z3 and Lean for every integer including negatives.  TRUST SURFACE:
pure Z3 (no uninterpreted functions, no axioms, no Lean dispatch).

Template.  Straight-line `SB(n=2)` (an if/else): one branch sets
`result := 1`, the other `result := 0`.  This is the scalar analogue of
`abs.py` / `verina_basic_3`.  The guard candidate lists let the
synthesizer *discover* the reference guard `n % 2 == 0` (and its
complement) against distractors that either violate the post or fail to
cover all of `n`.
"""
from synth import Problem, SB, Var, solve


# The evenness predicate, reused in the post and the guards.
_EVEN = "n % 2 == 0"


PROBLEM = Problem(
    description = (
        "Given an integer n, return true iff n is even."
    ),

    template = SB(n=2),
    inputs   = [Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    # Literal port of VERINA's two-implication postcondition, with the
    # Bool result modeled as int 0/1 and evenness encoded as `%`.
    post     = (
        f"Implies(result == 1, ({_EVEN})) and "
        f"Implies(result == 0, not ({_EVEN}))"
    ),
    atoms = {
        # Branch 0 — "even" ⇒ result := 1.
        "g@B0.0": [
            _EVEN,                   # the reference implementation
            "n % 2 != 0",            # distractor — unsound (would set 1 for odds)
            "n > 0",                 # distractor — unsound cover
        ],
        "s@B0.0": [{"result": "1"}],

        # Branch 1 — "not even" ⇒ result := 0.
        "g@B0.1": [
            "n % 2 != 0",            # complement of the reference
            _EVEN,                   # distractor — fails to cover
            "n < 0",                 # distractor — unsound cover
        ],
        "s@B0.1": [{"result": "0"}],
    },
    max_solutions = 4,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_26/lean/SynthLean/Y2Corpus/verina_basic_26",
    wedge_threshold = 200,
    solver_timeout_ms = 60_000,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    print(f"wall: {time.monotonic() - t:.1f}s")
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for idx, sol in enumerate(result.solutions):
        print(f"── solution #{idx} (score={sol.score:g}) ──")
        print(sol.code)
        print()
