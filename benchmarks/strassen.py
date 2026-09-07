"""Strassen's 2×2 — POPL'10 §5.2.

Synthesize a 2×2 matrix multiplication body with seven intermediate
products kept as locals (matching POPL'10 Fig 2(a) verbatim).

Spec:
    Pre  : true
    Post : c11 == a11*b11 + a12*b21
         ∧ c12 == a11*b12 + a12*b22
         ∧ c21 == a21*b11 + a22*b21
         ∧ c22 == a21*b12 + a22*b22

The atom uses the **SSA / sequential** transition format: a list of
single-key dicts.  Each entry assigns one variable; later entries
may reference earlier LHS (so `c11 = v1 + v4 - v5 + v7` references
the freshly-computed `v_i`).  Constraint generation inlines the
intermediates symbolically.

Three candidates:

    #0 Strassen with v_i intermediates (7 multiplications)  ← valid
    #1 naive 8-mult, parallel dict form                      ← valid
    #2 all zeros                                              ← invalid
"""
from synth import Problem, SB, Var, solve


_STRASSEN_SSA = [
    {"v1": "(a11 + a22)*(b11 + b22)"},
    {"v2": "(a21 + a22)*b11"},
    {"v3": "a11*(b12 - b22)"},
    {"v4": "a22*(b21 - b11)"},
    {"v5": "(a11 + a12)*b22"},
    {"v6": "(a21 - a11)*(b11 + b12)"},
    {"v7": "(a12 - a22)*(b21 + b22)"},
    {"c11": "v1 + v4 - v5 + v7"},
    {"c12": "v3 + v5"},
    {"c21": "v2 + v4"},
    {"c22": "v1 + v3 - v2 + v6"},
]

_NAIVE_PARALLEL = {
    "c11": "a11*b11 + a12*b21",
    "c12": "a11*b12 + a12*b22",
    "c21": "a21*b11 + a22*b21",
    "c22": "a21*b12 + a22*b22",
    # v_i preserved by absence from this dict (x' = x).
}

_ALL_ZEROS = {
    "c11": "0", "c12": "0", "c21": "0", "c22": "0",
}


PROBLEM = Problem(
    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("a11", "a12", "a21", "a22",
                          "b11", "b12", "b21", "b22")],
    outputs  = [Var(n, "int", "output")
                for n in ("c11", "c12", "c21", "c22")],
    locals   = [Var(f"v{i}", "int", "local") for i in range(1, 8)],
    pre      = "true",
    post     = ("c11 == a11*b11 + a12*b21 and "
                "c12 == a11*b12 + a12*b22 and "
                "c21 == a21*b11 + a22*b21 and "
                "c22 == a21*b12 + a22*b22"),
    atoms = {
        "s@B0": [
            _STRASSEN_SSA,
            _NAIVE_PARALLEL,
            _ALL_ZEROS,
        ],
    },
    max_solutions = 5,
    expected_solutions = 2,
    expected_lean_hits = 0,
    solver_timeout_ms = 120_000,
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
