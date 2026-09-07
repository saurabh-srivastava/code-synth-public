"""karatsuba_gf2_deg2 — L2.1b warmup from OPEN_PRBS.md.

Multiply two degree-2 polynomials over GF(2):
    P(x) = p0 + p1·x + p2·x²
    Q(x) = q0 + q1·x + q2·x²
yielding their degree-4 product
    R(x) = r0 + r1·x + r2·x² + r3·x³ + r4·x⁴
over GF(2), where addition is XOR and multiplication is AND.
Each variable is a single bit (0 or 1).

Spec:
    Pre  : 0 ≤ pi, qi ≤ 1 for all i ∈ {0, 1, 2}
    Post : r0 == p0*q0
         ∧ r1 == (p0*q1 + p1*q0) % 2
         ∧ r2 == (p0*q2 + p1*q1 + p2*q0) % 2
         ∧ r3 == (p1*q2 + p2*q1) % 2
         ∧ r4 == p2*q2

Multiplication-count landscape:
    Naive            : 9 multiplications.
    Karatsuba-style  : 6 multiplications (this benchmark).
    Open question    : whether 5 is achievable over GF(2) is
                       genuinely **open** — this is the L2.1b
                       discovery target.

The 6-mult Karatsuba derivation
-------------------------------
Split p = α(x) + p2·x² where α = p0 + p1·x (degree 1).
Similarly q = β(x) + q2·x².  Then

    p·q = α·β + (α·q2 + p2·β)·x² + p2·q2·x⁴

Compute α·β (deg-1 × deg-1) with Karatsuba's 3 mults:
    m0a = p0·q0
    m0c = (p0⊕p1)·(q0⊕q1)
    m1  = p1·q1
Compute (α + p2)·(β + q2) (also deg-1 × deg-1) with 3 mults
EXCEPT the middle one (p1·q1) is the SAME as m1 above — share:
    m1a = (p0⊕p2)·(q0⊕q2)
    m1c = (p0⊕p1⊕p2)·(q0⊕q1⊕q2)
    (middle = m1, shared)
Plus the leading term:
    m2  = p2·q2

Total: 6 unique multiplications.

Output coefficients (using `−` = `+` in GF(2)):
    r0 = m0a
    r1 = m0c ⊕ m0a ⊕ m1                  (cross of α·β)
    r2 = (m1a ⊕ m0a ⊕ m2) ⊕ m1           (mid coefficient
                                            (α·q2+p2·β) + p1·q1)
    r3 = m1c ⊕ m0c ⊕ m1a ⊕ m0a           (cross of (α+p2)·(β+q2)
                                            minus already-counted)
    r4 = m2

Verification: hand-checked on (p0,p1,p2)=(1,0,1), (q0,q1,q2)=(1,1,0):
    True product (1+x²)(1+x) = 1 + x + x² + x³.
    m0a=1, m0c=0, m1=0, m1a=0, m1c=0, m2=0.
    r0=1, r1=(0+1+0)%2=1, r2=(0+1+0+0)%2=1, r3=(0+0+0+1)%2=1, r4=0. ✓

Smoke test purpose
------------------
L2.1b's warmup: demonstrate that the framework reaches n=3
(degree-2 polynomial multiplication) over GF(2).  If 6-mult and
9-mult both verify, the next step is the **discovery target**:
discrim-test 5-mult candidates.  But that requires §G.5's
parametric m_i template extension — bilinear-form holes with
coefficient holes from {0, 1} — which is multi-week IR work.

Three candidates here:

    #0  Karatsuba-style 6-mult SSA    ← expected valid
    #1  Naive 9-mult parallel          ← expected valid
    #2  All zeros                       ← expected invalid

If both #0 and #1 verify, the framework's reach extends from
deg-1 to deg-2 over GF(2) without modification.  The actual
discovery work (5-mult search) begins after §G.5 lands.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None
# 2026-05-20: L2.1b warmup.  Verify 6-mult Karatsuba and
# 9-mult naive both succeed.  5-mult is the discovery target;
# needs §G.5 parametric m_i.


_KARATSUBA_GF2_DEG2 = [
    # 6 multiplications, all in GF(2) (m*n for 0/1 vals = m·n
    # for integer mult; addition reduces mod 2 via % 2).
    {"m0a": "p0 * q0"},
    {"m0c": "((p0 + p1) % 2) * ((q0 + q1) % 2)"},
    {"m1":  "p1 * q1"},
    {"m1a": "((p0 + p2) % 2) * ((q0 + q2) % 2)"},
    {"m1c": "((p0 + p1 + p2) % 2) * ((q0 + q1 + q2) % 2)"},
    {"m2":  "p2 * q2"},
    {"r0":  "m0a"},
    {"r1":  "(m0c + m0a + m1) % 2"},
    {"r2":  "(m1a + m0a + m2 + m1) % 2"},
    {"r3":  "(m1c + m0c + m1a + m0a) % 2"},
    {"r4":  "m2"},
]


_NAIVE_PARALLEL = {
    "r0": "p0 * q0",
    "r1": "(p0 * q1 + p1 * q0) % 2",
    "r2": "(p0 * q2 + p1 * q1 + p2 * q0) % 2",
    "r3": "(p1 * q2 + p2 * q1) % 2",
    "r4": "p2 * q2",
}


_ALL_ZEROS = {
    "r0": "0", "r1": "0", "r2": "0", "r3": "0", "r4": "0",
}


PROBLEM = Problem(
    description = (
        "Multiply two degree-2 polynomials over GF(2): "
        "P(x) = p0 + p1·x + p2·x² and Q(x) = q0 + q1·x + q2·x², "
        "yielding their degree-4 product R(x) = r0 + r1·x + "
        "r2·x² + r3·x³ + r4·x⁴, with all coefficients in {0, 1} "
        "and GF(2) arithmetic (+ is XOR, * is AND)."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("p0", "p1", "p2", "q0", "q1", "q2")],
    outputs  = [Var(n, "int", "output")
                for n in ("r0", "r1", "r2", "r3", "r4")],
    locals   = [Var(n, "int", "local")
                for n in ("m0a", "m0c", "m1", "m1a", "m1c", "m2")],

    pre  = ("0 <= p0 and p0 <= 1 and "
            "0 <= p1 and p1 <= 1 and "
            "0 <= p2 and p2 <= 1 and "
            "0 <= q0 and q0 <= 1 and "
            "0 <= q1 and q1 <= 1 and "
            "0 <= q2 and q2 <= 1"),
    post = ("r0 == p0 * q0 and "
            "r1 == (p0 * q1 + p1 * q0) % 2 and "
            "r2 == (p0 * q2 + p1 * q1 + p2 * q0) % 2 and "
            "r3 == (p1 * q2 + p2 * q1) % 2 and "
            "r4 == p2 * q2"),

    atoms = {
        "s@B0": [
            _KARATSUBA_GF2_DEG2,
            _NAIVE_PARALLEL,
            _ALL_ZEROS,
        ],
    },
    max_solutions = 5,
    expected_solutions = None,
    solver_timeout_ms = 900_000,  # 15 min — larger post, more cases.
)


if __name__ == "__main__":
    print(f"karatsuba_gf2_deg2 — XFAIL_REASON: {XFAIL_REASON!r}")
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
