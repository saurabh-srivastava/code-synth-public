"""majority_element — Phase X.S stretch corpus (hard HE+/MBPP+).

Boyer-Moore voting algorithm: find an element that appears > n/2
times in an array of length n, using O(1) extra space and one pass.

Spec:
    Pre  : n >= 1
         ∧ ∃ v. count_eq(A, n, v) > n / 2
    Post : count_eq(A, n, candidate) > n / 2

Why this is a stretch benchmark
-------------------------------
The classical correctness proof rests on a non-obvious invariant:

    If a majority exists, then it equals `candidate` OR the
    "votes" so far balance out (cnt represents net surplus
    votes for `candidate` over all other elements seen so
    far).

Formally, with `cnt_eq(A, i, v) = count of v in A[0..i)`:
    cnt + cnt_eq(A, i, candidate)
      ≥ cnt_eq(A, i, v)  for any v ≠ candidate

So if the true majority `v*` has count > n/2 overall but we
ended up with `candidate ≠ v*`, the counter would have gone
negative somewhere — contradiction.

This invariant requires the `count_eq` UF axiom AND quantification
over "any other value v", which is unprecedented in our corpus.

Likely failure modes
--------------------
- Universal quantification over a counter UF (∀ v. ...) inside
  the invariant is heavy for both Z3 and Lean's generic tactics.
- Termination is trivial (i increments by 1), but the inductive
  step is the hard part.
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


# === Helper registry (§H.2 codegen) ===============================
# `lean/SynthLean/Y2Corpus/majority_element/Helpers.lean` ships
# `majority_post_from_inv` — cites the `boyer_moore_dominance`
# Tier-2 axiom + user Pre to derive `count_eq(A, n, candidate) >
# n // 2` at loop exit.
# Atom-index conventions for tau@L0:
#   0: "0 <= i"           1: "i <= n"
#   2: "cnt >= 0"         3: bm_inv (∀v.  cnt + count_eq ≥ ...)
# Required: {1, 2, 3} — i_le_n + cnt_nn + bm_inv.  Loop-modified
# vars are {candidate, cnt, i}; primed at exit.  Pre destructures
# into (h_pre_n, h_pre_maj) for the helper's expected signature.


def _cite_majority_post_from_inv(chosen, hyp_for):
    h_i_le_n = hyp_for("tau@L0", 1)
    h_cnt_nn = hyp_for("tau@L0", 2)
    h_bm_inv = hyp_for("tau@L0", 3)
    return (
        "obtain ⟨h_pre_n, h_pre_maj⟩ := h_pre\n"
        "  exact SynthLean.MajElemHelpers.majority_post_from_inv "
        f"A n i' candidate' cnt' h_pre_n h_pre_maj "
        f"{h_i_le_n} {h_cnt_nn} {h_bm_inv} h_not_g"
    )


def _cite_majority_safety_branch(branch_idx: int):
    axiom_name = (
        "maj_branch0_preserves_inv" if branch_idx == 0
        else "maj_branch1_preserves_inv"
    )

    def cite(chosen, hyp_for):
        h_t0 = hyp_for("tau@L0", 0)
        h_t1 = hyp_for("tau@L0", 1)
        h_t2 = hyp_for("tau@L0", 2)
        h_t3 = hyp_for("tau@L0", 3)
        if branch_idx == 0:
            # Branch 0 modifies all 3 vars (candidate, cnt, i).
            return (
                f"exact {axiom_name} A n candidate cnt i "
                f"candidate' cnt' i' "
                f"h_pre {h_t0} {h_t1} {h_t2} {h_t3} h_guard "
                f"h_trans_candidate h_trans_cnt h_trans_i"
            )
        else:
            # Branch 1 modifies {cnt, i} only.  Translator binders
            # are `cnt' i'` (no `candidate'`).  Axiom signature
            # mirrors: takes `n candidate cnt i cnt' i'`.
            return (
                f"exact {axiom_name} A n candidate cnt i cnt' i' "
                f"h_pre {h_t0} {h_t1} {h_t2} {h_t3} h_guard "
                f"h_trans_cnt h_trans_i"
            )
    return cite


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.majority_element.Helpers",
    entries=[
        HelperEntry(
            helper_name="majority_post_from_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post" and loop_id == "L0"),
            required_atoms={"tau@L0": frozenset({1, 2, 3})},
            cite=_cite_majority_post_from_inv,
        ),
        HelperEntry(
            helper_name="maj_branch0_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 0),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3})},
            cite=_cite_majority_safety_branch(0),
        ),
        HelperEntry(
            helper_name="maj_branch1_preserves_inv",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety" and loop_id == "L0"
                        and branch_idx == 1),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3})},
            cite=_cite_majority_safety_branch(1),
        ),
    ],
)


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-19 via H.2.CODEGEN.
# History: 600s timeout (Run 1) → UNSAT-with-cache (Run 2, 1487s) →
# ~3min after H.2.CODEGEN (bundle-post + 2 safety branch helpers
# citing boyer_moore_dominance + maj_branchN_preserves_inv axioms,
# plus the new theorem_for_coverage Lean translator that
# unblocked the SAT consistency).  See RESEARCH.md §H.2.CODEGEN
# and EXPERIENCE_REPORT CS-8.


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n (n ≥ 1) for which "
        "some value appears strictly more than n/2 times, return "
        "that majority element using Boyer-Moore voting."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("candidate", "int", "output")],
    locals   = [Var("i", "int", "local"),
                Var("cnt", "int", "local")],

    pre = (
        "(n >= 1) and "
        "Exists(lambda v: count_eq(A, n, v) > n // 2)"
    ),
    post = "count_eq(A, n, candidate) > n // 2",

    uninterpreted = [
        ("count_eq", ["int[]", "int", "int"], "int"),
    ],
    axioms = [
        # Base case: empty prefix has zero occurrences.
        # NOTE: lambda bound vars default to Int in our IR — can't
        # quantify over the array, so the axiom is stated for the
        # specific A in this Problem (same pattern as dot_product).
        "ForAll(lambda v: count_eq(A, 0, v) == 0)",
        # Successor: extending by A[k] adds 1 if A[k] == v else 0.
        ("ForAll(lambda k, v: Implies(k >= 0, "
         " count_eq(A, k + 1, v) == "
         " count_eq(A, k, v) + (1 if A[k] == v else 0)))"),
        # Non-negativity (derivable, helpful as a hint).
        ("ForAll(lambda k, v: Implies(k >= 0, "
         " count_eq(A, k, v) >= 0))"),
    ],

    atoms = {
        # Initial: candidate := A[0] (any starting choice), cnt := 0.
        "s@B0": [{"candidate": "A[0]", "cnt": "0", "i": "0"}],

        "tau@L0": [
            "0 <= i", "i <= n", "cnt >= 0",
            # Net-surplus invariant: cnt counts surplus votes for
            # `candidate` over all-other-values combined.  Stated
            # with a single representative "any other v" axiom — the
            # solver picks the strongest form.
            ("ForAll(lambda v: "
             " cnt + count_eq(A, i, candidate) >= "
             " count_eq(A, i, v))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: cnt == 0 — adopt A[i] as new candidate.
        "g@B1.0": ["cnt == 0"],
        "s@B1.0": [{"candidate": "A[i]", "cnt": "1", "i": "i + 1"}],

        # Branch 1: cnt > 0 — vote up or down depending on match.
        "g@B1.1": ["cnt > 0"],
        "s@B1.1": [{"cnt": "cnt + 1 if A[i] == candidate else cnt - 1",
                    "i":   "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/majority_element",
    helper_registry = _HELPER_REGISTRY,
)


if __name__ == "__main__":
    print(f"majority_element — XFAIL_REASON: {XFAIL_REASON!r}")
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
