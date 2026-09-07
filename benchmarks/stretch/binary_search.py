"""binary_search — Phase X.S stretch corpus (hard HE+/MBPP+).

Given a sorted integer array A of length n and a target x, return
the index of an occurrence of x in A, or -1 if x is not present.

Spec:
    Pre  : n >= 0  ∧  sortedness(A, n)
           (∀ p, q. 0 ≤ p ≤ q < n  ⇒  A[p] ≤ A[q])
    Post : (idx == -1  ∧  ∀ k. 0 ≤ k < n  ⇒  A[k] != x)
         ∨ (0 ≤ idx < n  ∧  A[idx] == x)

Why this is a stretch benchmark
-------------------------------
The classical proof of binary-search correctness keeps the
invariant "if x is in A at all, it lives in A[lo..hi]" — an
existential property that's awkward for SMT.  We weaken to the
strictly-ordered formulation:

    ForAll k. 0 ≤ k < lo  ⇒  A[k] < x
    ForAll k. hi < k < n  ⇒  A[k] > x

These two quantified atoms, combined with sortedness in the
pre, give the synthesizer enough to verify the not-found case
when (lo > hi).  The found case (A[mid] == x) terminates the
loop via the `found` flag and emits `idx := mid`.

Likely failure modes
--------------------
- Z3 wedges on the quantified atoms + integer-division `mid`
  computation.  We try Lean fallthrough; if generic tactics
  can't close the inductive class, curate `.solved.lean`
  companions in `lean/SynthLean/Y2Corpus/binary_search/`.
- Ranking is `hi - lo + 1` (≥ 0 at every τ-consistent state,
  strictly decreases on either branch).
"""
from synth import Problem, SB, Loop, Var, solve


# XFAIL_REASON tracks the LATEST known blocker — `None` means we
# expect this benchmark to fully synthesize and verify under the
# stretch budget.  Set to a short string describing the blocker if
# we determine the benchmark exceeds current capabilities.
XFAIL_REASON: str | None = None  # VERIFIED 2026-05-17.
# Verified via the 3-phase template (init → search-loop →
# post-check).  Synthesizer found a solution in ~30s.
#
# REAL CAPABILITY GAP SURFACED (banked for future framework work):
# The 'found-flag' pattern — branch 0 sets `found := 1` but
# doesn't shrink the window, exiting via the AND-guarded loop
# condition — fails our framework's per-branch ranking-decrease
# check.  The check fires unconditionally, requiring ϕ to
# strictly decrease at EVERY branch.  In the found branch ϕ
# stays equal; we'd need POPL'10's vacuous-Fpre ranking
# refinement (Phase 3.J for recursion) extended to loops:
# decrease only required when the next-iter loop-guard remains
# true.  The 3-phase workaround sidesteps this by collapsing
# the window unconditionally and doing the found-check after
# the loop.  Banked as a candidate framework enhancement; not
# blocking for binary_search itself.


PROBLEM = Problem(
    description = (
        "Given a sorted integer array A of length n (n ≥ 0) and a "
        "target x, return an index where A[idx] == x, or -1 if x "
        "isn't present."
    ),

    # Three-phase template: init → search-loop → post-check.
    # The search loop collapses the window to lo == hi + 1 via
    # ≤/> comparisons (no early exit), maintaining the invariant
    # "x lives in [lo, hi] if anywhere".  Post-check examines
    # A[lo - 1] to decide whether to set idx or leave it at -1.
    template = SB() >> Loop(SB(n=2)) >> SB(n=2),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("x", "int", "input")],
    outputs  = [Var("idx", "int", "output")],
    locals   = [Var("lo", "int", "local"),
                Var("hi", "int", "local"),
                Var("mid", "int", "local")],

    pre = (
        "(n >= 0) and "
        "ForAll(lambda p, q: Implies("
        "  0 <= p and p <= q and q < n, A[p] <= A[q]))"
    ),
    post = (
        "((idx == -1) and "
        " ForAll(lambda k: Implies(0 <= k and k < n, A[k] != x))) or "
        "((0 <= idx) and (idx < n) and (A[idx] == x))"
    ),

    atoms = {
        # Phase 1: init.  lo := 0, hi := n - 1, idx := -1.
        "s@B0": [{"lo": "0", "hi": "n - 1", "idx": "-1"}],

        # Phase 2: search loop.  Loop invariant maintains:
        #   - [0, lo) contains only values ≤ x
        #   - (hi, n) contains only values > x  (strict)
        # Window narrows by 1 per iteration.  Exits at lo > hi.
        "tau@L0": [
            "0 <= lo",
            "hi < n",
            "n >= 0",
            "lo <= hi + 1",
            ("ForAll(lambda p, q: Implies("
             " 0 <= p and p <= q and q < n, A[p] <= A[q]))"),
            ("ForAll(lambda k: Implies("
             " 0 <= k and k < lo, A[k] <= x))"),
            ("ForAll(lambda k: Implies("
             " hi < k and k < n, A[k] > x))"),
        ],
        "g@L0":   ["lo <= hi"],
        "phi@L0": ["hi - lo + 1"],
        # Branch 0: A[mid] <= x — narrow right.
        "g@B1.0": ["A[(lo + hi) // 2] <= x"],
        "s@B1.0": [{"mid": "(lo + hi) // 2",
                    "lo":  "((lo + hi) // 2) + 1"}],
        # Branch 1: A[mid] > x — narrow left.
        "g@B1.1": ["A[(lo + hi) // 2] > x"],
        "s@B1.1": [{"mid": "(lo + hi) // 2",
                    "hi":  "((lo + hi) // 2) - 1"}],

        # Phase 3: post-check.  After loop, [0, lo) holds values ≤ x.
        # If x is present, it's at A[lo - 1].
        # Branch 0: lo > 0 AND A[lo-1] == x — record idx.
        "g@B2.0": ["(lo >= 1) and (A[lo - 1] == x)"],
        "s@B2.0": [{"idx": "lo - 1"}],
        # Branch 1: x not present — leave idx == -1.
        "g@B2.1": ["(lo == 0) or (A[lo - 1] != x)"],
        "s@B2.1": [{}],
    },
    max_solutions = 1,
    expected_solutions = None,  # stretch — count is informational
    solver_timeout_ms = 1_800_000,  # 30 min — stretch budget
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/binary_search",
)


if __name__ == "__main__":
    print(f"binary_search — XFAIL_REASON: {XFAIL_REASON!r}")
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED (expected if XFAIL_REASON set): {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1 if XFAIL_REASON is None else 0)
    print(f"Found {len(result.solutions)} solution(s).")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
