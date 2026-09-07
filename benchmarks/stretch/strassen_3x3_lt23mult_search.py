"""strassen_3x3_lt23mult_search — Phase X.S edge-of-open research
benchmark.

Search for a 22-product (or fewer) 3×3 integer matrix multiplication
algorithm.  Laderman 1976 gave 23 products; whether ≤22 over Z is
still open.  Current best lower bounds (Smirnov 2013, Heun, others):
  - 19 ≤ R(3,3,3) ≤ 23 over Z
  - Bilinear rank 21 is achievable over ℂ (Smirnov 2013).
  - Over Z, no algorithm with ≤22 multiplications is known.

What this benchmark is and isn't
---------------------------------
**This is NOT a true bilinear-rank search.**  Our IR doesn't
support parametric coefficient search (each transition is a
concrete SSA chain, not a template with unknown coefficients).
The "search" is over a small hand-crafted set of candidate
22-product chains.

The 23 hand-crafted candidates below each drop ONE of Laderman's
products and adopt "best-effort" output formulas for the c_ij's.
**All 23 candidates are expected UNSAT** — we proved offline
(via linear-algebra over the 81 a_pq*b_rs basis) that dropping
any single m_i from Laderman's 23 leaves a 22-product subset
whose linear span does NOT contain all 9 c_ij's.

Why run it anyway
-----------------
1. **Discrimination guard.**  If the synthesizer ACCEPTS any
   22-product candidate, it's either a real discovery (huge
   result) or — much more likely — a synthesizer soundness bug.
   This benchmark surfaces either case.

2. **Research data point.**  Runtime measures how fast the
   PLDI'09 attribute-class reduction enumerates and rejects 23
   candidates per check.  Sets a baseline for future
   parametric-template extensions.

3. **Search-space limitation as a phase-future signal.**  The
   benchmark concretely demonstrates what's NOT searchable
   without IR support for parametric coefficient holes.  Real
   discovery requires either:
   - **Parametric m_i templates** — each m_i's coefficients
     drawn from a search space (e.g., {-1, 0, 1}).  IR
     extension needed.
   - **Smirnov-style approximate-rank lifting** — use
     non-integer or symbolic coefficients (ℂ-valued algorithms).
     Far outside our current IR scope.

EXPECT_NO_SOLUTION = True
=========================
Like the karatsuba/toom3 discrimination tests, this benchmark
treats SAT as a DISCRIM-FAIL (would be a soundness bug) and
UNSAT as DISCRIM-PASS (the expected outcome).
"""
from synth import Problem, SB, Var


EXPECT_NO_SOLUTION = True


# All 23 Laderman m_i products.
LADERMAN_PRODUCTS = {
    1:  "(a11 + a12 + a13 - a21 - a22 - a32 - a33)*b22",
    2:  "(a11 - a21)*(b22 - b12)",
    3:  "a22*(-b11 + b12 + b21 - b22 - b23 - b31 + b33)",
    4:  "(-a11 + a21 + a22)*(b11 - b12 + b22)",
    5:  "(a21 + a22)*(-b11 + b12)",
    6:  "a11*b11",
    7:  "(-a11 + a31 + a32)*(b11 - b13 + b23)",
    8:  "(-a11 + a31)*(b13 - b23)",
    9:  "(a31 + a32)*(-b11 + b13)",
    10: "(a11 + a12 + a13 - a22 - a23 - a31 - a32)*b23",
    11: "a32*(-b11 + b13 + b21 - b22 - b23 - b31 + b32)",
    12: "(-a13 + a32 + a33)*(b22 + b31 - b32)",
    13: "(a13 - a33)*(b22 - b32)",
    14: "a13*b31",
    15: "(a32 + a33)*(-b31 + b32)",
    16: "(-a13 + a22 + a23)*(b23 + b31 - b33)",
    17: "(a13 - a23)*(b23 - b33)",
    18: "(a22 + a23)*(-b31 + b33)",
    19: "a12*b21",
    20: "a23*b32",
    21: "a21*b13",
    22: "a31*b12",
    23: "a33*b33",
}


def make_22mult_candidate(skip_idx: int) -> list:
    """SSA chain dropping m_{skip_idx}, with output formulas as in
    Laderman (which will be incomplete for at least one c_ij when
    the dropped m_i was part of its expansion)."""
    # Map output formulas (Laderman's, may reference the skipped m_i).
    outputs = {
        "c11": "m6 + m14 + m19",
        "c12": "m1 + m4 + m5 + m6 + m12 + m14 + m15",
        "c13": "m6 + m7 + m9 + m10 + m14 + m16 + m18",
        "c21": "m2 + m3 + m4 + m6 + m14 + m16 + m17",
        "c22": "m2 + m4 + m5 + m6 + m20",
        "c23": "m14 + m16 + m17 + m18 + m21",
        "c31": "m6 + m7 + m8 + m11 + m12 + m13 + m14",
        "c32": "m12 + m13 + m14 + m15 + m22",
        "c33": "m6 + m7 + m8 + m9 + m23",
    }
    # Replace any reference to the skipped m_i with "0" — this is the
    # "naive omission" attempt.  The synthesizer must reject these
    # whenever the omitted product is load-bearing for any c_ij.
    skip_term = f"m{skip_idx}"
    fixed_outputs = {}
    for k, v in outputs.items():
        if skip_term in v.split(" + "):
            # Drop that term; this output is now "wrong" (won't equal c_ij).
            new_terms = [t for t in v.split(" + ") if t != skip_term]
            fixed_outputs[k] = " + ".join(new_terms) if new_terms else "0"
        else:
            fixed_outputs[k] = v

    ssa = []
    # All 22 remaining m_i's (filtered).
    for idx, expr in LADERMAN_PRODUCTS.items():
        if idx != skip_idx:
            ssa.append({f"m{idx}": expr})
    # Output formulas.
    for k, v in fixed_outputs.items():
        ssa.append({k: v})
    return ssa


# 23 candidate chains, each dropping a different m_i.
CANDIDATES = [make_22mult_candidate(k) for k in range(1, 24)]


PROBLEM = Problem(
    description = (
        "DISCRIMINATION/RESEARCH TEST — must return NoSolution.  "
        "23 hand-crafted 22-product 3x3 matmul candidates (each "
        "dropping one of Laderman's 23 products); none are "
        "mathematically valid (proved by linear-algebra rank check)."
    ),

    template = SB(),
    inputs   = [Var(f"a{i}{j}", "int", "input")
                for i in (1, 2, 3) for j in (1, 2, 3)]
             + [Var(f"b{i}{j}", "int", "input")
                for i in (1, 2, 3) for j in (1, 2, 3)],
    outputs  = [Var(f"c{i}{j}", "int", "output")
                for i in (1, 2, 3) for j in (1, 2, 3)],
    locals   = [Var(f"m{i}", "int", "local") for i in range(1, 24)],

    pre  = "true",
    post = " and ".join(
        f"c{i}{j} == a{i}1*b1{j} + a{i}2*b2{j} + a{i}3*b3{j}"
        for i in (1, 2, 3) for j in (1, 2, 3)
    ),

    atoms = {"s@B0": CANDIDATES},
    max_solutions = 3,
    solver_timeout_ms = 600_000,  # 10 min
)


if __name__ == "__main__":
    from synth import solve
    print("strassen_3x3_lt23mult_search — EXPECT_NO_SOLUTION = True")
    print(f"  search space: 23 candidates (each drops 1 of Laderman's m_i)")
    result = solve(PROBLEM)
    if result:
        print(f"DISCRIM-FAIL: {len(result.solutions)} candidate(s) verified!")
        print(f"  This would be a 22-mult algorithm — major discovery,")
        print(f"  but more likely a synthesizer soundness bug.")
        raise SystemExit(1)
    print(f"DISCRIM-PASS: all 23 candidates rejected ({result.reason})")
