"""Diagnostic 2: two polymul_3 calls with computed args.

Goal: verify the combination of polymul_3 calls with computed
args (GF(2) XOR) works.  This is closer to the n=5 Karatsuba
recipe but simpler.
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


# Recipe: read coeff [0] from two distinct polymul_3 calls.
# r0 should equal a0*b0 (from m_lo[0]).
# r1 should equal ((a0+a3)%2) * ((b0+b3)%2) (from m_mix[0]).
_RECIPE = [
    {"s_a0": "(a0 + a3) % 2"},
    {"s_b0": "(b0 + b3) % 2"},
    {"m_lo":  "polymul_3(a0, a1, a2, b0, b1, b2)"},
    {"m_mix": "polymul_3(s_a0, a1, a2, s_b0, b1, b2)"},
    {"r0": "m_lo[0]"},
    {"r1": "m_mix[0]"},
]


PROBLEM = Problem(
    description = "Diagnostic 2: two polymul_3 calls with one having computed args.",
    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("a0", "a1", "a2", "a3",
                          "b0", "b1", "b2", "b3")],
    outputs  = [Var(n, "int", "output") for n in ("r0", "r1")],
    locals   = ([Var("s_a0", "int", "local"),
                 Var("s_b0", "int", "local")]
                + [Var(n, "int[]", "local") for n in ("m_lo", "m_mix")]),
    pre = (" and ".join(f"0 <= {v} and {v} <= 1"
                        for v in ("a0", "a1", "a2", "a3",
                                  "b0", "b1", "b2", "b3"))),
    post = (
        "r0 == a0 * b0 and "
        "r1 == ((a0 + a3) % 2) * ((b0 + b3) % 2)"
    ),
    uninterpreted = _UF,
    axioms = _AXIOMS,
    atoms = {"s@B0": [_RECIPE]},
    max_solutions = 2,
    expected_solutions = None,
    solver_timeout_ms = 300_000,
)


if __name__ == "__main__":
    print("Diagnostic 2: two polymul_3 calls + computed-arg version.")
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
