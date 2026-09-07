"""Diagnostic: minimal axiom-application test.

Goal: verify just polymul_3 axiom unfolds correctly.  Recipe:
just CALL polymul_3, read its outputs, output them directly.
Post: outputs match the polymul_3 spec (which the axioms
state).

If THIS verifies, the axiom path works for polymul_3.  If
not, the issue is at the basic axiom-application level.
"""
from synth import Problem, SB, Var, solve


_UF = [
    ("polymul_3", ["int", "int", "int", "int", "int", "int"], "int[]"),
]

_AXIOMS = [
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[0] == a0 * b0)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[1] == (a0 * b1 + a1 * b0) % 2)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[2] == "
     "  (a0 * b2 + a1 * b1 + a2 * b0) % 2)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[3] == (a1 * b2 + a2 * b1) % 2)"),
    ("ForAll(lambda a0, a1, a2, b0, b1, b2: "
     " polymul_3(a0, a1, a2, b0, b1, b2)[4] == a2 * b2)"),
]


_RECIPE = [
    {"m": "polymul_3(a0, a1, a2, b0, b1, b2)"},
    {"r0": "m[0]"},
    {"r1": "m[1]"},
    {"r2": "m[2]"},
    {"r3": "m[3]"},
    {"r4": "m[4]"},
]


PROBLEM = Problem(
    description = "Diagnostic: verify polymul_3 axiom unfolds.",
    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("a0", "a1", "a2", "b0", "b1", "b2")],
    outputs  = [Var(n, "int", "output")
                for n in ("r0", "r1", "r2", "r3", "r4")],
    locals   = [Var("m", "int[]", "local")],
    pre = (" and ".join(f"0 <= {v} and {v} <= 1"
                        for v in ("a0", "a1", "a2", "b0", "b1", "b2"))),
    post = (
        "r0 == a0 * b0 and "
        "r1 == (a0 * b1 + a1 * b0) % 2 and "
        "r2 == (a0 * b2 + a1 * b1 + a2 * b0) % 2 and "
        "r3 == (a1 * b2 + a2 * b1) % 2 and "
        "r4 == a2 * b2"
    ),
    uninterpreted = _UF,
    axioms = _AXIOMS,
    atoms = {"s@B0": [_RECIPE]},
    max_solutions = 2,
    expected_solutions = None,
    solver_timeout_ms = 300_000,
)


if __name__ == "__main__":
    print("Diagnostic: just polymul_3 + read-back + Pre-bounded inputs.")
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
    else:
        print(f"Found {len(result.solutions)} solution(s).")
        for n, sol in enumerate(result.solutions):
            print(f"── solution #{n} (score={sol.score:g}) ──")
            print(sol.code)
