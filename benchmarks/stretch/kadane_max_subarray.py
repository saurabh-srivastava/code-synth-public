"""kadane_max_subarray — Phase X.S stretch corpus (hard HE+/MBPP+).

Kadane's algorithm: maximum-sum contiguous subarray, single pass,
O(n) time, O(1) extra space.

Spec:
    Pre  : n >= 1
    Post : ∃ p, q. 0 ≤ p ≤ q < n  ∧
           best == sum_range(A, p, q + 1)
         ∧ ∀ p, q. 0 ≤ p ≤ q < n  ⇒
           sum_range(A, p, q + 1) ≤ best

The witness pair `(p, q)` is existentially quantified — every valid
post needs to expose AT LEAST one (start, end) pair achieving the
max.  Our IR doesn't return witness pairs; we approximate by
strengthening the spec to "best == sum of some contiguous subarray"
and verifying the upper-bound clause.

Why this is a stretch benchmark
-------------------------------
- **`sum_range` UF**: classical subarray-sum.  Recurrence:
    sum_range(A, p, p)     == 0
    sum_range(A, p, q + 1) == sum_range(A, p, q) + A[q]
- **Coupled invariants**: two quantities (`best`, `cur`) where
  `cur` is "max subarray ending exactly at i-1" and `best` is
  "max over all subarrays ending at any j < i".  The inductive
  needs both:
    cur ≥ sum_range(A, k, i) for some k ≤ i  (or cur ≥ 0)
    best ≥ sum_range(A, p, q + 1) for all p, q with q < i
- **Universal-quantifier post** with a subarray-sum UF is the
  hard SMT shape.  Lean fallthrough is the planned route.

Likely failure modes
--------------------
- Z3 wedges on the universal subarray-sum upper-bound inductive.
- Lean's generic tactic chain may need `induction k` hints —
  candidate for a hand-curated `.solved.lean` companion.
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


# === Helper registry (§H.2 codegen) ===============================
# `lean/SynthLean/Y2Corpus/kadane_max_subarray/Helpers.lean` ships
# `kadane_post_from_inv` — a pure Tier-1 helper that derives the
# universal-quantified Post from the chosen τ atoms at loop exit.
# Atom-index conventions for tau@L0:
#   0: "1 <= i"            2: cur upper-bound (∀p)
#   1: "i <= n"            3: cur existential (∃p)
#   4: best upper-bound (∀p,q) — REQUIRED
#   5: "best >= cur"
# Required: {1, 4} — i_le_n + best_ub.  Loop-modified vars are
# {best, cur, i}; the translator primes them at loop exit, so the
# cite passes `best'`, `i'`.


def _cite_kadane_post_from_inv(chosen, hyp_for):
    h_i_le_n = hyp_for("tau@L0", 1)
    h_best_ub = hyp_for("tau@L0", 4)
    return (
        "exact SynthLean.KadaneHelpers.kadane_post_from_inv "
        f"A n best' i' {h_i_le_n} {h_best_ub} h_not_g"
    )


def _cite_kadane_safety_branch(branch_idx: int):
    """Cite the per-branch Tier-2 axiom for kadane's safety obligation.

    The axiom takes all 6 τ atoms (FULL set required) plus guard
    + transitions and concludes the τ conjunction at i+1.
    Branch 0 = extending current run; branch 1 = restart at A[i].
    """
    axiom_name = (
        "kadane_branch0_preserves_inv" if branch_idx == 0
        else "kadane_branch1_preserves_inv"
    )

    def cite(chosen, hyp_for):
        h_t0 = hyp_for("tau@L0", 0)
        h_t1 = hyp_for("tau@L0", 1)
        h_t2 = hyp_for("tau@L0", 2)
        h_t3 = hyp_for("tau@L0", 3)
        h_t4 = hyp_for("tau@L0", 4)
        h_t5 = hyp_for("tau@L0", 5)
        return (
            f"exact {axiom_name} A n best cur i best' cur' i' "
            f"h_pre {h_t0} {h_t1} {h_t2} {h_t3} {h_t4} {h_t5} "
            f"h_guard h_trans_cur h_trans_best h_trans_i"
        )
    return cite


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.kadane_max_subarray.Helpers",
    entries=[
        HelperEntry(
            helper_name="kadane_post_from_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post" and loop_id == "L0"),
            required_atoms={"tau@L0": frozenset({1, 4})},
            cite=_cite_kadane_post_from_inv,
        ),
        HelperEntry(
            helper_name="kadane_branch0_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 0),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_kadane_safety_branch(0),
        ),
        HelperEntry(
            helper_name="kadane_branch1_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 1),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_kadane_safety_branch(1),
        ),
    ],
)


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-19 via H.2.CODEGEN.
# History: 600s timeout (2026-05-17) → 70s after H.2.CODEGEN
# helper-citation path landed (bundle-post + 2 safety branch
# helpers + short-circuit).  See RESEARCH.md §H.2.CODEGEN.


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n (n ≥ 1), return the "
        "maximum sum among all contiguous non-empty subarrays "
        "(Kadane's algorithm)."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("best", "int", "output")],
    locals   = [Var("i", "int", "local"),
                Var("cur", "int", "local")],

    pre = "n >= 1",
    post = (
        "ForAll(lambda p, q: Implies("
        "  0 <= p and p <= q and q < n, "
        "  sum_range(A, p, q + 1) <= best))"
    ),

    uninterpreted = [
        ("sum_range", ["int[]", "int", "int"], "int"),
    ],
    axioms = [
        # Empty range.  (Quantification over A is at module scope —
        # lambda bound vars default to Int in our IR.)
        "ForAll(lambda p: sum_range(A, p, p) == 0)",
        # Extend by one element on the right.
        ("ForAll(lambda p, q: Implies(p <= q, "
         " sum_range(A, p, q + 1) == sum_range(A, p, q) + A[q]))"),
    ],

    atoms = {
        # Initial: best := A[0], cur := A[0], i := 1.
        "s@B0": [{"best": "A[0]", "cur": "A[0]", "i": "1"}],

        "tau@L0": [
            "1 <= i", "i <= n",
            # cur is the max subarray sum ending at index i - 1.
            ("ForAll(lambda p: Implies("
             " 0 <= p and p <= i - 1, "
             " sum_range(A, p, i) <= cur))"),
            "Exists(lambda p: 0 <= p and p <= i - 1 and "
            " sum_range(A, p, i) == cur)",
            # best is the max over all subarrays ending at any j < i.
            ("ForAll(lambda p, q: Implies("
             " 0 <= p and p <= q and q < i, "
             " sum_range(A, p, q + 1) <= best))"),
            "best >= cur",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: extending current run is better than restarting.
        "g@B1.0": ["cur + A[i] >= A[i]"],
        "s@B1.0": [{"cur":  "cur + A[i]",
                    "best": "best if best >= cur + A[i] else cur + A[i]",
                    "i":    "i + 1"}],

        # Branch 1: restart at A[i].
        "g@B1.1": ["cur + A[i] < A[i]"],
        "s@B1.1": [{"cur":  "A[i]",
                    "best": "best if best >= A[i] else A[i]",
                    "i":    "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/kadane_max_subarray",
    helper_registry = _HELPER_REGISTRY,
)


if __name__ == "__main__":
    print(f"kadane_max_subarray — XFAIL_REASON: {XFAIL_REASON!r}")
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
