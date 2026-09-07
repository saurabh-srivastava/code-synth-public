"""boolean_matmul_3x3 — Phase X.S stretch corpus (edge of open).

Boolean matrix multiplication for 3×3 Boolean matrices over the
semiring (∨, ∧).  Naive uses 27 ANDs and 18 ORs to compute the 9
output entries.  Whether fewer AND-gates suffice is an open
combinatorial-circuit question for small sizes — the famous
"Boolean tensor rank" gap.

Spec:
    Pre  : Each input a_ij, b_ij ∈ {0, 1} (Boolean encoded as int)
    Post : c_ij == OR over k of (a_ik AND b_kj)

This benchmark mirrors `benchmarks/stretch/strassen_3x3_laderman.py`
but over the Boolean semiring.  Three candidate transitions:

    #0  Naive 27-AND, 18-OR              ← expected valid
    #1  Strassen-style attempt           ← almost certainly invalid
                                            (Strassen subtracts; no
                                            subtraction in Boolean)
    #2  All zeros                         ← invalid

The interesting case is whether we can express a non-trivial
candidate (e.g., one using common-subexpression elimination on
the AND/OR DAG) and have the synthesizer verify it.

Why this is a stretch benchmark
-------------------------------
- **Bit-level ops in the IR.**  Our IR treats `int` as
  unbounded Z3 Int.  Boolean operations (∧, ∨) over
  {0, 1}-valued ints can be encoded as `min(a, b)` and
  `max(a, b)` or as `a * b` and `a + b - a * b`.  Synthesizer
  needs to accept these in transition expressions; we use the
  `*` / `+ ... - *` encoding.
- **Novel-algorithm potential.**  If the synthesizer accepts a
  non-trivial template (e.g., one with 22 ANDs via shared
  subexpressions), and Z3 verifies it correct, that's a
  genuine combinatorial-circuit result — albeit a small one.

Likely failure modes
--------------------
- Z3 will treat the Boolean encoding as nonlinear arithmetic.
  Whether it can prove `(min(a, b))` correctness for the {0,1}
  domain depends on whether the precondition `a ∈ {0, 1}`
  reaches the validity check.
- This benchmark mostly tests SHAPE; we don't expect to
  discover novel algorithms in Phase X.S.
"""
from synth import Problem, SB, Var, solve


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-17.
# Naive 27-AND 18-OR candidate (score=9) verifies; all-zeros
# correctly rejected.  Z3 handles the min/max Boolean encoding
# with the {0,1}-domain precondition automatically.  Runtime:
# ~5s.  Discovery thread (fewer ANDs via shared subexpressions)
# is open — a parametric template search would test the
# combinatorial-circuit lower-bound question for 3x3 BMM.


# Naive 27-AND 18-OR.  AND ≡ min, OR ≡ max for {0,1}-valued ints.
def _and(a, b): return f"({a} if {a} <= {b} else {b})"   # min
def _or(a, b):  return f"({a} if {a} >= {b} else {b})"   # max


def _naive_c(i, j):
    """OR over k of (a_ik AND b_kj) for k ∈ {1, 2, 3}."""
    t1 = _and(f"a{i}1", f"b1{j}")
    t2 = _and(f"a{i}2", f"b2{j}")
    t3 = _and(f"a{i}3", f"b3{j}")
    return _or(_or(t1, t2), t3)


_NAIVE_PARALLEL = {
    f"c{i}{j}": _naive_c(i, j)
    for i in (1, 2, 3) for j in (1, 2, 3)
}


_ALL_ZEROS = {f"c{i}{j}": "0" for i in (1, 2, 3) for j in (1, 2, 3)}


PROBLEM = Problem(
    description = (
        "Compute C = A·B where A, B are 3×3 Boolean matrices "
        "(entries ∈ {0, 1}) over the (∨, ∧) semiring.  Encoded "
        "as int with the precondition a_ij, b_ij ∈ {0, 1}."
    ),

    template = SB(),
    inputs   = [Var(f"a{i}{j}", "int", "input")
                for i in (1, 2, 3) for j in (1, 2, 3)]
             + [Var(f"b{i}{j}", "int", "input")
                for i in (1, 2, 3) for j in (1, 2, 3)],
    outputs  = [Var(f"c{i}{j}", "int", "output")
                for i in (1, 2, 3) for j in (1, 2, 3)],

    pre = " and ".join(
        f"(0 <= a{i}{j} and a{i}{j} <= 1) and "
        f"(0 <= b{i}{j} and b{i}{j} <= 1)"
        for i in (1, 2, 3) for j in (1, 2, 3)
    ),
    # Post specifies the result in terms of the same min/max
    # encoding — symmetric to the candidate transitions.
    post = " and ".join(
        f"c{i}{j} == " + _naive_c(i, j)
        for i in (1, 2, 3) for j in (1, 2, 3)
    ),

    atoms = {
        "s@B0": [_NAIVE_PARALLEL, _ALL_ZEROS],
    },
    max_solutions = 3,
    expected_solutions = None,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    print(f"boolean_matmul_3x3 — XFAIL_REASON: {XFAIL_REASON!r}")
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
