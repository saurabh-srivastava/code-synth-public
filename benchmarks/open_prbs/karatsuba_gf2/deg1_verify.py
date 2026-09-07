"""karatsuba_gf2_deg1 — L2.1a from OPEN_PRBS.md (smoke test).

Multiply two degree-1 polynomials over GF(2):
    P(x) = p0 + p1·x
    Q(x) = q0 + q1·x
yielding their degree-2 product
    R(x) = r0 + r1·x + r2·x²
over GF(2), where addition is XOR and multiplication is AND.
Each variable is a single bit (0 or 1).

Spec:
    Pre  : 0 ≤ p0, p1, q0, q1 ≤ 1
    Post : r0 == p0 * q0                   (AND)
         ∧ r1 == (p0 * q1 + p1 * q0) % 2   (XOR of two ANDs)
         ∧ r2 == p1 * q1                   (AND)

Naive over GF(2): 4 multiplications (4 ANDs, 1 XOR).
Karatsuba over GF(2): 3 multiplications (3 ANDs, 4 XORs).
  m0 := p0 * q0
  m1 := p1 * q1
  m2 := ((p0 + p1) % 2) * ((q0 + q1) % 2)    -- (p0⊕p1)·(q0⊕q1)
  r0 := m0
  r2 := m1
  r1 := (m0 + m1 + m2) % 2                    -- in GF(2), - = +

In GF(2), subtraction = addition (since x + x = 0), so the
Karatsuba "r1 = m2 - m0 - m1" becomes "r1 = m2 + m0 + m1" in
GF(2) — equivalent to `(m0 + m1 + m2) % 2` over integer
arithmetic with 0/1 values.

Smoke test purpose
------------------
L2.1a from OPEN_PRBS.md: demonstrate that the framework can
handle GF(2) field arithmetic by encoding the field elements
as integer values restricted to {0, 1} and using `% 2` for
GF(2) addition (XOR).  Multiplication in GF(2) for 0/1 values
is identical to integer multiplication, so it needs no special
encoding.

Three candidates:

    #0  Karatsuba 3-mult SSA          ← expected valid
    #1  Naive 4-mult parallel         ← expected valid
    #2  All zeros                      ← expected invalid

This mirrors the structure of `benchmarks/stretch/karatsuba_deg2.py`
(the over-ℤ version) at the GF(2) scale.  If both #0 and #1
verify, the framework reaches GF(2) field axioms via integer
encoding — the precondition for L2.1b (5-mult search for
n=3 over GF(2), which requires §G.5's parametric m_i
extension).

The 3-mult-vs-4-mult result is well-known and settled for
n=1 over GF(2); this benchmark is the smoke test that
validates the encoding, NOT a discovery target.  The discovery
work begins at L2.1b (n=3 below 6 mults over GF(2)).
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None  # 2026-05-20: L2.1a smoke test.


_KARATSUBA_GF2 = [
    {"m0": "p0 * q0"},
    {"m1": "p1 * q1"},
    {"m2": "((p0 + p1) % 2) * ((q0 + q1) % 2)"},
    {"r0": "m0"},
    {"r2": "m1"},
    {"r1": "(m0 + m1 + m2) % 2"},
]


_NAIVE_PARALLEL = {
    "r0": "p0 * q0",
    "r1": "(p0 * q1 + p1 * q0) % 2",
    "r2": "p1 * q1",
}


_ALL_ZEROS = {"r0": "0", "r1": "0", "r2": "0"}


PROBLEM = Problem(
    description = (
        "Multiply two degree-1 polynomials over GF(2): "
        "P(x) = p0 + p1·x and Q(x) = q0 + q1·x, yielding "
        "their degree-2 product R(x) = r0 + r1·x + r2·x², "
        "with all coefficients in {0, 1} and GF(2) "
        "arithmetic (+ is XOR, * is AND)."
    ),

    template = SB(),
    inputs   = [Var(n, "int", "input")
                for n in ("p0", "p1", "q0", "q1")],
    outputs  = [Var(n, "int", "output") for n in ("r0", "r1", "r2")],
    locals   = [Var(f"m{i}", "int", "local") for i in range(3)],

    pre  = ("0 <= p0 and p0 <= 1 and "
            "0 <= p1 and p1 <= 1 and "
            "0 <= q0 and q0 <= 1 and "
            "0 <= q1 and q1 <= 1"),
    post = ("r0 == p0 * q0 and "
            "r1 == (p0 * q1 + p1 * q0) % 2 and "
            "r2 == p1 * q1"),

    atoms = {
        "s@B0": [
            _KARATSUBA_GF2,
            _NAIVE_PARALLEL,
            _ALL_ZEROS,
        ],
    },
    max_solutions = 5,
    expected_solutions = None,
    solver_timeout_ms = 600_000,  # 10 min budget.
)


if __name__ == "__main__":
    print(f"karatsuba_gf2_deg1 — XFAIL_REASON: {XFAIL_REASON!r}")
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
