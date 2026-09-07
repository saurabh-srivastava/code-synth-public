"""merge_two_sorted — Phase X.S stretch corpus (hard HE+/MBPP+).

Interleave two sorted input arrays A (length n) and B (length p)
into one sorted output C of length n + p containing all elements
from A and B.

Spec:
    Pre  : n >= 0  ∧  p >= 0  ∧  sorted(A, n)  ∧  sorted(B, p)
    Post : sorted(C, n + p)

The "sorted" predicate is encoded as an uninterpreted Boolean
function `is_sorted(D, k)` with recursive axioms over k:
    is_sorted(D, 0) = True                       (vacuous)
    is_sorted(D, 1) = True                       (single element)
    is_sorted(D, k+1) = is_sorted(D, k) ∧ D[k-1] <= D[k]
                                                 (k >= 1)

This matches the encoding pattern used by kadane (sum_range),
majority (count_eq), and modular_exp (pow): a UF with a
recurrence axiom that triggers the H.2.CODEGEN dispatch path
(_axiom_heavy_lean_path) and benefits from helper short-circuit.

The earlier encoding (ForAll(lambda r, s: ...) directly in τ)
made the τ atoms quantified, which (a) didn't trigger the
axiom-heavy path, and (b) made Z3's per-class checks quadratic
in atom count.  The new encoding pushes the universal into the
UF axioms (out of τ) and keeps τ atoms quantifier-free.

Why this is still a stretch benchmark
-------------------------------------
Three sorted invariants in play simultaneously (A, B, C).
The inductive needs:
    1. is_sorted(C, i+j) (prefix sorted).
    2. C[i+j-1] ≤ A[i] (newly-emitted ≤ next A; load-bearing
                        for the extending axiom).
    3. C[i+j-1] ≤ B[j] (similar for B).
Plus chain-bundle-style propagation across the 3 sequential
loops (merge → drain B → drain A), which is the multi-loop
chain shape (different from FW's NESTED loops).

Likely behavior
---------------
With the UF encoding, axiom-heavy path engages.  Safety /
bundle-entry / bundle-post obligations go through Lean dispatch;
without helpers registered, they hit the generic tactic chain.
Lean's `omega` + axiom rewriting handles `is_sorted` recurrences
well.  Ranking and coverage stay on Z3 (fast).
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


# === Helper registry (§H.2 codegen) ===============================
# Tier-2 axioms in lean/SynthLean/Y2Corpus/merge_two_sorted/Helpers.lean
# encode the per-branch invariant preservation for L0's SB(n=2).
# Atom indices in tau@L0 (must match order in `atoms` below):
#   0: "0 <= i"            4: "is_sorted(C, i + j) == 1"
#   1: "i <= n"            5: "Implies(i + j > 0, C[i+j-1] <= A[i])"
#   2: "0 <= j"            6: "Implies(i + j > 0, C[i+j-1] <= B[j])"
#   3: "j <= p"


def _cite_merge_safety_branch(branch_idx: int):
    axiom_name = (
        "merge_branch0_preserves_inv" if branch_idx == 0
        else "merge_branch1_preserves_inv"
    )

    def cite(chosen, hyp_for):
        h_t0 = hyp_for("tau@L0", 0)
        h_t1 = hyp_for("tau@L0", 1)
        h_t2 = hyp_for("tau@L0", 2)
        h_t3 = hyp_for("tau@L0", 3)
        h_t4 = hyp_for("tau@L0", 4)
        h_t5 = hyp_for("tau@L0", 5)
        h_t6 = hyp_for("tau@L0", 6)
        if branch_idx == 0:
            # Branch 0 modifies {C, i}; j unchanged.
            return (
                f"exact {axiom_name} n p i j i' A B C C' "
                f"h_pre {h_t0} {h_t1} {h_t2} {h_t3} {h_t4} {h_t5} {h_t6} "
                f"h_guard h_trans_C h_trans_i"
            )
        else:
            # Branch 1 modifies {C, j}; i unchanged.
            return (
                f"exact {axiom_name} n p i j j' A B C C' "
                f"h_pre {h_t0} {h_t1} {h_t2} {h_t3} {h_t4} {h_t5} {h_t6} "
                f"h_guard h_trans_C h_trans_j"
            )
    return cite


def _cite_merge_l1_drain_b(chosen, hyp_for):
    h_t0 = hyp_for("tau@L1", 0)  # 0 ≤ i
    h_t1 = hyp_for("tau@L1", 1)  # i ≤ n
    h_t2 = hyp_for("tau@L1", 2)  # 0 ≤ j
    h_t3 = hyp_for("tau@L1", 3)  # j ≤ p
    h_t4 = hyp_for("tau@L1", 4)  # is_sorted C (i+j) = 1
    h_t5 = hyp_for("tau@L1", 5)  # last ≤ B[j]
    return (
        "exact merge_l1_drain_b_preserves_inv n p i j j' A B C C' "
        f"h_pre {h_t0} {h_t1} {h_t2} {h_t3} {h_t4} {h_t5} "
        "h_guard h_trans_C h_trans_j"
    )


def _cite_merge_l2_drain_a(chosen, hyp_for):
    h_t0 = hyp_for("tau@L2", 0)
    h_t1 = hyp_for("tau@L2", 1)
    h_t2 = hyp_for("tau@L2", 2)
    h_t3 = hyp_for("tau@L2", 3)
    h_t4 = hyp_for("tau@L2", 4)
    h_t5 = hyp_for("tau@L2", 5)
    return (
        "exact merge_l2_drain_a_preserves_inv n p i j i' A B C C' "
        f"h_pre {h_t0} {h_t1} {h_t2} {h_t3} {h_t4} {h_t5} "
        "h_guard h_trans_C h_trans_i"
    )


def _cite_merge_l1_entry_chain(chosen, hyp_for):
    """Cite merge_l1_entry_chain for sc7 (L1 entry, chain-aware).

    Chain = [B0(init), L0(abstract)].  3 states (s0, s1, s2).
    Goal: τ@L1 atoms at s2.  All conjuncts follow directly from
    τ@L0 hypotheses.
    """
    return (
        "exact merge_l1_entry_chain "
        "n_s0 p_s0 i_s0 j_s0 A_s0 B_s0 C_s0 "
        "n_s1 p_s1 i_s1 j_s1 A_s1 B_s1 C_s1 "
        "n_s2 p_s2 i_s2 j_s2 A_s2 B_s2 C_s2 "
        "h_pre "
        "h_i0_trans_i h_i0_trans_j "
        "h_i0_frame_n h_i0_frame_p h_i0_frame_A h_i0_frame_B h_i0_frame_C "
        "h_i1_L0_tau_0 h_i1_L0_tau_1 h_i1_L0_tau_2 h_i1_L0_tau_3 "
        "h_i1_L0_tau_4 h_i1_L0_tau_5 h_i1_L0_tau_6 "
        "h_i1_L0_not_g "
        "h_i1_L0_frame_n h_i1_L0_frame_p h_i1_L0_frame_A h_i1_L0_frame_B"
    )


def _cite_merge_l2_entry_chain(chosen, hyp_for):
    """Cite merge_l2_entry_chain for sc11 (L2 entry, chain-aware).

    The chain-aware translator names hypotheses by chain position
    + loop_id + atom_idx (e.g., `h_i1_L0_tau_0`).  The cite emits
    a one-shot `exact` invoking the axiom with all bound names.
    """
    return (
        "exact merge_l2_entry_chain "
        "n_s0 p_s0 i_s0 j_s0 A_s0 B_s0 C_s0 "
        "n_s1 p_s1 i_s1 j_s1 A_s1 B_s1 C_s1 "
        "n_s2 p_s2 i_s2 j_s2 A_s2 B_s2 C_s2 "
        "n_s3 p_s3 i_s3 j_s3 A_s3 B_s3 C_s3 "
        "h_pre "
        "h_i0_trans_i h_i0_trans_j "
        "h_i0_frame_n h_i0_frame_p h_i0_frame_A h_i0_frame_B h_i0_frame_C "
        "h_i1_L0_tau_0 h_i1_L0_tau_1 h_i1_L0_tau_2 h_i1_L0_tau_3 "
        "h_i1_L0_tau_4 h_i1_L0_tau_5 h_i1_L0_tau_6 "
        "h_i1_L0_not_g "
        "h_i1_L0_frame_n h_i1_L0_frame_p h_i1_L0_frame_A h_i1_L0_frame_B "
        "h_i2_L1_tau_0 h_i2_L1_tau_1 h_i2_L1_tau_2 h_i2_L1_tau_3 "
        "h_i2_L1_tau_4 h_i2_L1_tau_5 "
        "h_i2_L1_not_g "
        "h_i2_L1_frame_n h_i2_L1_frame_p h_i2_L1_frame_i "
        "h_i2_L1_frame_A h_i2_L1_frame_B"
    )


def _cite_merge_final_post_chain(chosen, hyp_for):
    """Cite merge_final_post_chain for sc15 (final post, chain-aware)."""
    return (
        "exact merge_final_post_chain "
        "n_s0 p_s0 i_s0 j_s0 A_s0 B_s0 C_s0 "
        "n_s1 p_s1 i_s1 j_s1 A_s1 B_s1 C_s1 "
        "n_s2 p_s2 i_s2 j_s2 A_s2 B_s2 C_s2 "
        "n_s3 p_s3 i_s3 j_s3 A_s3 B_s3 C_s3 "
        "n_s4 p_s4 i_s4 j_s4 A_s4 B_s4 C_s4 "
        "h_pre "
        "h_i0_trans_i h_i0_trans_j "
        "h_i0_frame_n h_i0_frame_p h_i0_frame_A h_i0_frame_B h_i0_frame_C "
        "h_i1_L0_tau_0 h_i1_L0_tau_1 h_i1_L0_tau_2 h_i1_L0_tau_3 "
        "h_i1_L0_tau_4 h_i1_L0_tau_5 h_i1_L0_tau_6 "
        "h_i1_L0_not_g "
        "h_i1_L0_frame_n h_i1_L0_frame_p h_i1_L0_frame_A h_i1_L0_frame_B "
        "h_i2_L1_tau_0 h_i2_L1_tau_1 h_i2_L1_tau_2 h_i2_L1_tau_3 "
        "h_i2_L1_tau_4 h_i2_L1_tau_5 "
        "h_i2_L1_not_g "
        "h_i2_L1_frame_n h_i2_L1_frame_p h_i2_L1_frame_i "
        "h_i2_L1_frame_A h_i2_L1_frame_B "
        "h_i3_L2_tau_0 h_i3_L2_tau_1 h_i3_L2_tau_2 h_i3_L2_tau_3 "
        "h_i3_L2_tau_4 h_i3_L2_tau_5 "
        "h_i3_L2_not_g "
        "h_i3_L2_frame_n h_i3_L2_frame_p h_i3_L2_frame_j "
        "h_i3_L2_frame_A h_i3_L2_frame_B"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.merge_two_sorted.Helpers",
    entries=[
        HelperEntry(
            helper_name="merge_branch0_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 0),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6})},
            cite=_cite_merge_safety_branch(0),
        ),
        HelperEntry(
            helper_name="merge_branch1_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 1),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6})},
            cite=_cite_merge_safety_branch(1),
        ),
        HelperEntry(
            helper_name="merge_l1_drain_b_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L1"),
            required_atoms={"tau@L1": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_merge_l1_drain_b,
        ),
        HelperEntry(
            helper_name="merge_l2_drain_a_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L2"),
            required_atoms={"tau@L2": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_merge_l2_drain_a,
        ),
        # sc7 — L1 entry-bundle, chain-aware (single Loop in chain).
        HelperEntry(
            helper_name="merge_l1_entry_chain",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-entry"
                        and loop_id == "L1"),
            required_atoms={
                "tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6}),
                "tau@L1": frozenset({0, 1, 2, 3, 4, 5}),
            },
            cite=_cite_merge_l1_entry_chain,
        ),
        # sc11 — L2 entry-bundle, chain-aware (chained loop case).
        HelperEntry(
            helper_name="merge_l2_entry_chain",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-entry"
                        and loop_id == "L2"),
            required_atoms={
                "tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6}),
                "tau@L1": frozenset({0, 1, 2, 3, 4, 5}),
                "tau@L2": frozenset({0, 1, 2, 3, 4, 5}),
            },
            cite=_cite_merge_l2_entry_chain,
        ),
        # sc15 — final bundle-post, chain-aware.  Outermost loop_id
        # extracted to L0 (first τ ref in atom_refs).
        HelperEntry(
            helper_name="merge_final_post_chain",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post"
                        and loop_id == "L0"),
            required_atoms={
                "tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6}),
                "tau@L1": frozenset({0, 1, 2, 3, 4, 5}),
                "tau@L2": frozenset({0, 1, 2, 3, 4, 5}),
            },
            cite=_cite_merge_final_post_chain,
        ),
    ],
)


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-19 (v7: ~2 min, 1 solution).
# Earlier history:
#   v1: quantified τ atoms — 0 dumps in 10 min (Z3 wedged on
#       universal quantifier reasoning).
#   v2: re-encoded with is_sorted UF + recurrence axioms — 39 sc2
#       dumps; needed safety helpers.
#   v3-v5: added 4 safety inductive Tier-2 axioms (merge_branch0/1
#       _preserves_inv, merge_l1_drain_b, merge_l2_drain_a).
#   v6: 188 sc7 fallthrough dumps — bundle-entry/post hit the
#       translator's flat `theorem_for_entry_bundle` which raised
#       NotImplementedError on the chained-loop chain.
#   #167: chain-aware translator (theorem_for_entry_bundle_chain +
#       theorem_for_chain_bundle_chain) routes correctly when the
#       chain contains non-SB items OR the target is nested.
#   v7: added 3 chain-aware Tier-2 axioms (merge_l1_entry_chain,
#       merge_l2_entry_chain, merge_final_post_chain).  Synthesis
#       completes in ~2 min, finds the classical 4-phase merge.


PROBLEM = Problem(
    description = (
        "Given two sorted integer arrays A (length n) and B "
        "(length p), produce a sorted array C of length n + p "
        "containing all elements from A and B."
    ),

    # 4-phase template: init → merge-both → drain-B → drain-A.
    template = SB() >> Loop(SB(n=2)) >> Loop(SB()) >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("B", "int[]", "input"),
                Var("p", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local"),
                Var("j", "int", "local")],

    pre = (
        "(n >= 0) and (p >= 0) and "
        "is_sorted(A, n) == 1 and is_sorted(B, p) == 1"
    ),
    post = "is_sorted(C, n + p) == 1",

    uninterpreted = [
        # Boolean-valued UF: is_sorted(D, k) ∈ {0, 1} (Int-encoded
        # for IR compatibility — IR doesn't support typed lambda
        # bindings, so we can't universally quantify over D as
        # Array(Int, Int).  Workaround: per-array axioms (A, B, C
        # each).
        ("is_sorted", ["int[]", "int"], "int"),
    ],
    axioms = [
        # === Base cases for A, B, C (length 0 = vacuously sorted).
        "is_sorted(A, 0) == 1",
        "is_sorted(B, 0) == 1",
        "is_sorted(C, 0) == 1",
        # === Single-element base (length 1 always sorted).
        "is_sorted(A, 1) == 1",
        "is_sorted(B, 1) == 1",
        "is_sorted(C, 1) == 1",
        # === Recurrence for A: sorted(A, k+1) iff sorted(A, k)
        # AND A[k-1] ≤ A[k].  Requires k ≥ 1 so A[k-1] is defined.
        ("ForAll(lambda k: Implies(k >= 1, "
         " is_sorted(A, k + 1) == "
         " (1 if (is_sorted(A, k) == 1 and A[k - 1] <= A[k]) else 0)))"),
        # === Recurrence for B.
        ("ForAll(lambda k: Implies(k >= 1, "
         " is_sorted(B, k + 1) == "
         " (1 if (is_sorted(B, k) == 1 and B[k - 1] <= B[k]) else 0)))"),
        # === Recurrence for C (the output array, mutated during
        # synthesis; the same axiom applies post-mutation since C
        # is a fresh symbolic state per τ check).
        ("ForAll(lambda k: Implies(k >= 1, "
         " is_sorted(C, k + 1) == "
         " (1 if (is_sorted(C, k) == 1 and C[k - 1] <= C[k]) else 0)))"),
    ],

    atoms = {
        # Phase 1: init.
        "s@B0": [{"i": "0", "j": "0"}],

        # Phase 2: merge while BOTH arrays have elements.
        "tau@L0": [
            "0 <= i", "i <= n", "0 <= j", "j <= p",
            # Output prefix sorted (UF-application — no quantifier).
            "is_sorted(C, i + j) == 1",
            # Last emitted ≤ next A — gated on i < n.  Gating avoids
            # the boundary case i = n where A[n] is unconstrained by
            # is_sorted(A, n) = 1.  Vacuous when loop exits via i=n.
            "Implies((i + j > 0) and (i < n), C[i + j - 1] <= A[i])",
            # Last emitted ≤ next B — gated on j < p (symmetric).
            "Implies((i + j > 0) and (j < p), C[i + j - 1] <= B[j])",
        ],
        "g@L0":   ["(i < n) and (j < p)"],
        "phi@L0": ["(n - i) + (p - j)"],

        "g@B1.0": ["A[i] <= B[j]"],
        "s@B1.0": [{"C": "Update(C, i + j, A[i])", "i": "i + 1"}],
        "g@B1.1": ["A[i] > B[j]"],
        "s@B1.1": [{"C": "Update(C, i + j, B[j])", "j": "j + 1"}],

        # Phase 3: drain B (fires when A is exhausted; i = n).
        "tau@L1": [
            "0 <= i", "i <= n", "0 <= j", "j <= p",
            "is_sorted(C, i + j) == 1",
            "Implies((i + j > 0) and (j < p), C[i + j - 1] <= B[j])",
        ],
        "g@L1":   ["j < p"],
        "phi@L1": ["p - j"],
        "s@B2":   [{"C": "Update(C, i + j, B[j])", "j": "j + 1"}],

        # Phase 4: drain A (fires when B is exhausted; j = p).
        "tau@L2": [
            "0 <= i", "i <= n", "0 <= j", "j <= p",
            "is_sorted(C, i + j) == 1",
            "Implies((i + j > 0) and (i < n), C[i + j - 1] <= A[i])",
        ],
        "g@L2":   ["i < n"],
        "phi@L2": ["n - i"],
        "s@B3":   [{"C": "Update(C, i + j, A[i])", "i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/merge_two_sorted",
    helper_registry = _HELPER_REGISTRY,
)


if __name__ == "__main__":
    print(f"merge_two_sorted — XFAIL_REASON: {XFAIL_REASON!r}")
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
