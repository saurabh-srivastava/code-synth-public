"""Smoke tests for the §6.2 / §6.3 failure-mode channels.

We construct a pathological Problem that has no valid atom for the
loop invariant, and verify that the solver returns NoSolution carrying
unsat-core names and human-readable hints.
"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from synth import Problem, SB, Loop, Var, solve, NoSolution, SolveResult


def make_intsqrt(tau_atoms):
    return Problem(
        template = SB() >> Loop(SB()) >> SB(),
        inputs   = [Var("x", "int", "input")],
        outputs  = [Var("i", "int", "output")],
        locals   = [Var("v", "int", "local")],
        pre      = "x >= 1",
        post     = "(i - 1)*(i - 1) <= x and x < i*i",
        atoms = {
            "tau@L0": tau_atoms,
            "g@L0":   ["v <= x"],
            "phi@L0": ["x - (i - 1)*(i - 1)"],
            "s@B0":   [{"v": "1", "i": "1"}],
            "s@B1":   [{"v": "v + 2*i + 1", "i": "i + 1"}],
            "s@B2":   [ {} ],
        },
        max_solutions = 3,
    )


def test_sat_with_correct_atom():
    prob = make_intsqrt([
        "v == i*i and x >= (i - 1)*(i - 1) and i >= 1",
    ])
    r = solve(prob)
    assert isinstance(r, SolveResult), f"expected SolveResult, got {type(r).__name__}: {r}"
    assert len(r.solutions) == 1


def test_unsat_when_invariant_too_weak():
    """No invariant candidate is strong enough — expect NoSolution
    with structured hints describing the failure mode.

    Under CEGIS, `unsat_core` is empty (we don't use named assertions);
    the diagnostic signal is in `hints`.
    """
    prob = make_intsqrt([
        "true",                            # too weak: doesn't imply Fpost
        "i >= 1",                          # too weak
        "v >= x and i >= 1",               # wrong shape
    ])
    r = solve(prob)
    assert isinstance(r, NoSolution), f"expected NoSolution, got {type(r).__name__}"
    assert r.reason == "unsat"
    assert isinstance(r.hints, list) and len(r.hints) > 0, \
        f"expected hints, got {r.hints!r}"


if __name__ == "__main__":
    test_sat_with_correct_atom()
    print("✓ sat-with-correct-atom")
    test_unsat_when_invariant_too_weak()
    print("✓ unsat-with-weak-invariant")
    print("\nfailure-channel tests passed")
