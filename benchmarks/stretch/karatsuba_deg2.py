"""karatsuba_deg2 — Phase X.S stretch corpus (edge of open).

Polynomial multiplication of two degree-1 polynomials
(P = p0 + p1·x, Q = q0 + q1·x) computing the degree-2 product
R = r0 + r1·x + r2·x² using only 3 scalar multiplications
(Karatsuba 1962) instead of the naive 4.

Spec:
    Pre  : true
    Post : r0 == p0*q0
         ∧ r1 == p0*q1 + p1*q0
         ∧ r2 == p1*q1

The classical Karatsuba trick:
    m0 := p0 * q0
    m1 := p1 * q1
    m2 := (p0 + p1) * (q0 + q1)
    r0 := m0
    r2 := m1
    r1 := m2 - m0 - m1   (the cross term, derived from 3 mults)

Why this is a stretch benchmark
-------------------------------
Same shape as `benchmarks/strassen.py` (POPL'10 §5.2 2×2) at the
polynomial-multiplication scale.  Three candidates:

    #0  Karatsuba 3-mult SSA          ← expected valid
    #1  Naive 4-mult parallel         ← expected valid
    #2  All zeros                      ← expected invalid

If both #0 and #1 verify, we've replayed the Strassen lesson at
the polynomial-mult scale.  Real "discovery" would extend this
to Toom-3 (5 mults for degree-2 × degree-2 → degree-4) or to
larger Karatsuba/Toom-Cook variants where the optimal
multiplication count is research-active.

Note: degree-2 polynomial mult is a known and settled case
(Karatsuba's 3 multiplications is optimal for degree-1 × degree-1
over a field with char != 2).  We chose this case as the
proving-ground for the template+search machinery rather than
trying to discover a new algorithm here — the open territory
sits at larger polynomial degrees.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-17.
# Both candidates verify: #0 naive 4-mult (score=3, fewer SSA
# atoms) and #1 Karatsuba 3-mult (score=6).  Confirms the
# Strassen-style template-search pattern (POPL'10 §5.2) replays
# at the polynomial-multiplication scale.  Runtime: ~5s.


_KARATSUBA_SSA = [
    {"m0": "p0 * q0"},
    {"m1": "p1 * q1"},
    {"m2": "(p0 + p1) * (q0 + q1)"},
    {"r0": "m0"},
    {"r2": "m1"},
    {"r1": "m2 - m0 - m1"},
]


_NAIVE_PARALLEL = {
    "r0": "p0 * q0",
    "r1": "p0 * q1 + p1 * q0",
    "r2": "p1 * q1",
}


_ALL_ZEROS = {"r0": "0", "r1": "0", "r2": "0"}


PROBLEM = Problem(
    description = (
        "Multiply two degree-1 polynomials (P = p0 + p1·x, "
        "Q = q0 + q1·x) yielding their degree-2 product "
        "R = r0 + r1·x + r2·x²."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("p0", "p1", "q0", "q1")],
    outputs  = [Var(n, "int", "output") for n in ("r0", "r1", "r2")],
    locals   = [Var(f"m{i}", "int", "local") for i in range(3)],

    pre  = "true",
    post = ("r0 == p0 * q0 and "
            "r1 == p0 * q1 + p1 * q0 and "
            "r2 == p1 * q1"),

    atoms = {
        "s@B0": [
            _KARATSUBA_SSA,
            _NAIVE_PARALLEL,
            _ALL_ZEROS,
        ],
    },
    max_solutions = 5,
    expected_solutions = None,
    solver_timeout_ms = 600_000,  # 10 min — much smaller than DP
)


if __name__ == "__main__":
    print(f"karatsuba_deg2 — XFAIL_REASON: {XFAIL_REASON!r}")
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1 if XFAIL_REASON is None else 0)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
