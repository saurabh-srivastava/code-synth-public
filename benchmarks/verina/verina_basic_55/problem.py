"""verina_basic_55_Compare — VERINA-basic port (Compare).

Ported from VERINA task `verina_basic_55` (Compare; upstream
clover task_id Clover_compare).  Determine whether two integers
are equal.

VERINA signature (source of truth):
    Compare(a : Int, b : Int) -> Bool
VERINA precondition (task.lean, between @start/@end precond):
    True
VERINA reference code:
    if a = b then true else false
VERINA postcondition (task.lean, between @start/@end postcond):
    (a = b → result = true) ∧ (a ≠ b → result = false)

Framework encoding
------------------
    Pre  : true
    Post : Implies(a == b, result == 1) and
           Implies(a != b, result == 0)

NAMING MAP (VERINA -> ours):
    VERINA `a`      (Int, scalar)   -> our `a`      (int, the input)
    VERINA `b`      (Int, scalar)   -> our `b`      (int, the input)
    VERINA `result` (Bool)          -> our `result` (int, 0/1)

Bool->int modeling.  Our IR is integer-valued, so the Bool `result`
is modeled as an int with the convention `result == 1` ⇔ true,
`result == 0` ⇔ false.  The two transitions only ever assign 0 or 1,
so `result ∈ {0, 1}` holds in every satisfying solution — no separate
boolean-domain axiom needed.  This is the same Bool->int coding used
by the sibling predicate benchmarks `verina_basic_26_isEven` and
`verina_basic_3_isDivisibleBy11`.

SPEC-FIDELITY NOTE
------------------
The post is a LITERAL transcription of VERINA's postcondition under the
Bool->{0,1} coding: VERINA's `a = b → result = true` is our
`Implies(a == b, result == 1)`, and VERINA's `a ≠ b → result = false`
is our `Implies(a != b, result == 0)`.  Because `result ∈ {0, 1}` is
total, these two forward implications are together equivalent to the
biconditional `result == 1 ⇔ (a == b)`, so the encoded post captures
VERINA's postcond exactly.  Integer equality `a = b` is Z3's `a == b`
verbatim (no coercion — both `a` and `b` are Int scalars).  TRUST
SURFACE: pure Z3 (no uninterpreted functions, no axioms, no Lean
dispatch).

Template.  Straight-line `SB(n=2)` (an if/else): one branch sets
`result := 1`, the other `result := 0`.  This is the scalar analogue of
`abs.py` / `verina_basic_26_isEven`.  The guard candidate lists let the
synthesizer *discover* the reference guard `a == b` (and its
complement) against distractors that either violate the post or fail to
cover all of the (a, b) plane.
"""
from synth import Problem, SB, Var, solve


# The equality predicate, reused in the post and the guards.
_EQ = "a == b"


PROBLEM = Problem(
    description = (
        "Given two integers a and b, return true iff a equals b."
    ),

    template = SB(n=2),
    inputs   = [Var("a", "int", "input"),
                Var("b", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    # Literal port of VERINA's two-implication postcondition, with the
    # Bool result modeled as int 0/1.
    post     = (
        f"Implies(({_EQ}), result == 1) and "
        f"Implies(a != b, result == 0)"
    ),
    atoms = {
        # Branch 0 — "a equals b" ⇒ result := 1.
        "g@B0.0": [
            _EQ,                     # the reference implementation
            "a != b",                # distractor — unsound (would set 1 when unequal)
            "a > b",                 # distractor — unsound cover
        ],
        "s@B0.0": [{"result": "1"}],

        # Branch 1 — "a not equal b" ⇒ result := 0.
        "g@B0.1": [
            "a != b",                # complement of the reference
            _EQ,                     # distractor — fails to cover
            "a < b",                 # distractor — unsound cover
        ],
        "s@B0.1": [{"result": "0"}],
    },
    max_solutions = 4,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_55/lean/SynthLean/Y2Corpus/verina_basic_55",
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
