"""verina_basic_1 — hasOppositeSign (ported from VERINA-basic).

Upstream: VERINA `verina_basic_1` (dafny-synthesis task_id_58).

    signature : hasOppositeSign(a: Int, b: Int) -> Bool
    precond   : True
    reference : a * b < 0
    postcond  : (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
                (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)

i.e. `result` is true iff `a` and `b` have strictly opposite signs
(zero counts as neither positive nor negative).

Bool→int modeling.  Our IR is integer-valued, so the Bool `result`
is modeled as an int with the convention `result == 1` ⇔ true,
`result == 0` ⇔ false.  VERINA's postcondition (two conjoined
implications) maps directly onto that convention:

    Implies(opposite,      result == 1)   -- "opposite ⇒ result"
    Implies(not opposite,  result == 0)   -- "¬opposite ⇒ ¬result"

where `opposite ≡ (a < 0 and b > 0) or (a > 0 and b < 0)`.  The two
transitions only ever assign 0 or 1, so `result ∈ {0, 1}` holds in
every satisfying solution — no separate boolean-domain axiom needed.

Template.  Straight-line `SB(n=2)` (an if/else): one branch sets
`result := 1`, the other `result := 0`.  This is the scalar analogue
of `abs.py`.  The guard candidate lists let the synthesizer *discover*
the reference guard `a * b < 0` (a nonlinear fact Z3 must relate to
the explicit sign-case disjunction), alongside the explicit
sign-disjunction guard.  Distractor guards (`a < 0` / `a >= 0`) form a
complete+exclusive cover but violate the post, so they are rejected.
"""
from synth import Problem, SB, Var, solve


# The "strictly opposite signs" predicate, reused in the post.
_OPP = "(a < 0 and b > 0) or (a > 0 and b < 0)"


PROBLEM = Problem(
    description = (
        "Given two integers a and b, return true iff they have "
        "strictly opposite signs (one positive and the other "
        "negative). Zero is neither positive nor negative, so if "
        "either input is zero the result is false."
    ),

    template = SB(n=2),
    inputs   = [Var("a", "int", "input"), Var("b", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    pre      = "true",
    # Faithful port of VERINA's two-implication postcondition, with the
    # Bool result modeled as int 0/1.
    post     = (
        f"Implies(({_OPP}), result == 1) and "
        f"Implies(not ({_OPP}), result == 0)"
    ),
    atoms = {
        # Branch 0 — "opposite signs" ⇒ result := 1.
        "g@B0.0": [
            "a * b < 0",             # the reference implementation
            _OPP,                    # explicit sign-case disjunction
            "a < 0",                 # distractor (unsound cover)
        ],
        "s@B0.0": [{"result": "1"}],

        # Branch 1 — "same sign or a zero" ⇒ result := 0.
        "g@B0.1": [
            "a * b >= 0",            # complement of the reference
            f"not ({_OPP})",         # explicit complement
            "a >= 0",                # distractor (unsound cover)
        ],
        "s@B0.1": [{"result": "0"}],
    },
    max_solutions = 6,
    expected_solutions = 4,
    expected_lean_hits = 0,
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
