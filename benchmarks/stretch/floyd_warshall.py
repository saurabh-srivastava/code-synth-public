"""floyd_warshall — Phase X.S stretch corpus (edge of open).

All-pairs shortest paths via the Floyd-Warshall triple-nested
relaxation.  For each intermediate vertex k, update every (i, j)
pair to consider paths going through k:

    for k in [0, n):
        for i in [0, n):
            for j in [0, n):
                D[i][j] := min(D[i][j], D[i][k] + D[k][j])

Spec
----
    Pre  : n ≥ 0  ∧  ∀i, j. 0 ≤ i < n ∧ 0 ≤ j < n
                      → D[i][j] == D_in[i][j]
    Post : ∀i, j. 0 ≤ i < n ∧ 0 ≤ j < n
                  → D[i][j] == sp(D_in, i, j, n)

Where `sp(D_in, i, j, k)` is the shortest-path-via-k-intermediates
UF axiomatized via:
    sp(D_in, i, j, 0)     == D_in[i][j]
    sp(D_in, i, j, k + 1) ==
        if sp(D_in, i, j, k) ≤ sp(D_in, i, k, k) + sp(D_in, k, j, k)
        then sp(D_in, i, j, k)
        else sp(D_in, i, k, k) + sp(D_in, k, j, k)

Template (3-level nested loops)
-------------------------------
    SB                                      -- init k := 0
    >> Loop(                                -- while k < n
        SB                                  -- init i := 0
        >> Loop(                            -- while i < n
            SB                              -- init j := 0
            >> Loop(SB(n=2))                -- while j < n: cond. update
            >> SB                           -- i := i + 1
        )
        >> SB                               -- k := k + 1
    )

τ invariants (3 levels)
-----------------------
    τ_outer  (at outer-loop iter k):
        0 ≤ k ≤ n, n ≥ 0
        ∀i, j. 0 ≤ i, j < n  →  D[i][j] == sp(D_in, i, j, k)

    τ_middle (at middle-loop iter (k, i)):
        0 ≤ k < n, 0 ≤ i ≤ n, n ≥ 0
        rows fully updated:
          ∀i', j. 0 ≤ i' < i ∧ 0 ≤ j < n
                  →  D[i'][j] == sp(D_in, i', j, k + 1)
        rows still at k:
          ∀i', j. i ≤ i' < n ∧ 0 ≤ j < n
                  →  D[i'][j] == sp(D_in, i', j, k)

    τ_inner  (at inner-loop iter (k, i, j)):
        0 ≤ k < n, 0 ≤ i < n, 0 ≤ j ≤ n, n ≥ 0
        prior rows at k+1:
          ∀i', j'. 0 ≤ i' < i ∧ 0 ≤ j' < n
                   →  D[i'][j'] == sp(D_in, i', j', k + 1)
        current row, columns < j:
          ∀j'. 0 ≤ j' < j  →  D[i][j'] == sp(D_in, i, j', k + 1)
        current row, columns ≥ j:
          ∀j'. j ≤ j' < n  →  D[i][j'] == sp(D_in, i, j', k)
        future rows still at k:
          ∀i', j'. i + 1 ≤ i' < n ∧ 0 ≤ j' < n
                   →  D[i'][j'] == sp(D_in, i', j', k)

Why this is a stretch benchmark
-------------------------------
**Subcubic all-pairs shortest paths is open**: whether APSP can
be solved in O(n^{3-ε}) for some ε > 0 (without fast-matrix-mult
tricks) is a longstanding open problem.  The classical O(n³)
Floyd-Warshall is the warmup; verifying it exercises the
template framework on:
  - Triple-nested DP with quantified invariants on EACH level.
  - 4-argument UF (`sp` over D_in + i + j + k) with min-recurrence.
  - 2D Store + nested quantifiers.

`lcs.py` and `grid_paths.py` (2-loop UF) already time out.
Adding a third loop is multiplicative cost — expected to wedge.
The value is documenting what shape the IR / Z3 / Lean would
need to handle for APSP-style triple-DP.

Outcome (2026-05-18)
--------------------
  - **Synth wedge confirmed** at 15-min budget with 0 bytes of
    output — Z3 never returns from the very first per-class check
    (3D-DP + sp UF + axiom-1's branching recurrence exhausts
    axiom-instantiation budget).  No `.failed.lean` dumps
    produced because Z3 doesn't even reach UNKNOWN; it wedges
    before completing one validity check.
  - **Lean-side artifact complete**: 4 Tier-3 helpers landed in
    `lean/SynthLean/Y2Corpus/floyd_warshall/Helpers.lean`:
      * `floyd_warshall_post_from_inv`     (Tier-1, full proof)
      * `floyd_warshall_outer_inductive`   (Tier-1, full proof)
      * `floyd_warshall_middle_inductive`  (Tier-1, full proof)
      * `floyd_warshall_inner_inductive_axiom`  (Tier-2 named
        axiom; case analysis on (i vs k, j vs k, branch) using
        `sp_k_row_preserved`, `sp_k_col_preserved`, and axiom-1
        documented in the axiom statement; explicit Lean proof
        is future work).
    All four are imported in `SynthLean.lean` and build in 7.8s.
  - **What's blocked**: the synthesizer's PLDI'09 attribute-class
    enumeration cannot reach the per-subset shim path because Z3
    wedges before producing a single UNKNOWN.  Resolution requires
    either (a) §H.2 pattern-match cache to bypass Z3 for known-
    helper-citable shapes, or (b) driver-LLM directly proposing
    the τ subsets that match the helpers.
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


# === Helper registry (§H.2 codegen) ===============================
# Maps Tier-3 helpers in `lean/SynthLean/Y2Corpus/floyd_warshall/
# Helpers.lean` to the obligations they discharge.  The codegen
# layer cites these instead of running the generic tactic chain
# on matching τ subsets.
#
# Atom-index conventions (see _OUTER_TABLE_FILLED etc. below):
#   tau@L0: [0: "0 <= k", 1: "k <= n", 2: "n >= 0",
#            3: outer-table-filled]
#   tau@L1: [0..4: bookkeeping, 5: rows-updated, 6: rows-pending]
#   tau@L2: [0..6: bookkeeping, 7: prior-rows, 8: curr-done,
#            9: curr-pending, 10: future-rows]


def _cite_fw_l2_inductive_branch_0(chosen, hyp_for):
    """sc4 — L2 inductive branch 0 (no D update)."""
    return (
        "exact SynthLean.FloydWarshallHelpers.fw_l2_inductive_branch_0 "
        "n i j k D_in D j' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 "
        "h_tau_7 h_tau_8 h_tau_9 h_tau_10 h_guard h_trans_j"
    )


def _cite_fw_l2_inductive_branch_1(chosen, hyp_for):
    """sc6 — L2 inductive branch 1 (D updated via store2d)."""
    return (
        "exact SynthLean.FloydWarshallHelpers.fw_l2_inductive_branch_1 "
        "n i j k D_in D j' D' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 "
        "h_tau_7 h_tau_8 h_tau_9 h_tau_10 h_guard h_trans_D h_trans_j"
    )


def _cite_fw_l1_entry_chain(chosen, hyp_for):
    """sc1 — L1 entry (chain-aware). Goal: τ@L1 at s1."""
    return (
        "exact SynthLean.FloydWarshallHelpers.fw_l1_entry_chain "
        "n_s0 i_s0 j_s0 k_s0 D_in_s0 D_s0 "
        "n_s1 i_s1 j_s1 k_s1 D_in_s1 D_s1 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 h_enc_g "
        "h_i0_trans_i h_i0_frame_n h_i0_frame_j h_i0_frame_k "
        "h_i0_frame_D_in h_i0_frame_D"
    )


def _cite_fw_l2_entry_chain(chosen, hyp_for):
    """sc2 — L2 entry (chain-aware). Goal: τ@L2 at s1."""
    return (
        "exact SynthLean.FloydWarshallHelpers.fw_l2_entry_chain "
        "n_s0 i_s0 j_s0 k_s0 D_in_s0 D_s0 "
        "n_s1 i_s1 j_s1 k_s1 D_in_s1 D_s1 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 h_enc_tau_4 "
        "h_enc_tau_5 h_enc_tau_6 h_enc_g "
        "h_i0_trans_j h_i0_frame_n h_i0_frame_i h_i0_frame_k "
        "h_i0_frame_D_in h_i0_frame_D"
    )


def _cite_fw_l2_body_inductive_chain(chosen, hyp_for):
    """sc9 — L1's body around L2 (body inductive). Goal: τ@L1 at s3."""
    return (
        "exact SynthLean.FloydWarshallHelpers.fw_l2_body_inductive_chain "
        "n_s0 i_s0 j_s0 k_s0 D_in_s0 D_s0 "
        "n_s1 i_s1 j_s1 k_s1 D_in_s1 D_s1 "
        "n_s2 i_s2 j_s2 k_s2 D_in_s2 D_s2 "
        "n_s3 i_s3 j_s3 k_s3 D_in_s3 D_s3 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 h_enc_tau_4 "
        "h_enc_tau_5 h_enc_tau_6 h_enc_g "
        "h_i0_trans_j h_i0_frame_n h_i0_frame_i h_i0_frame_k "
        "h_i0_frame_D_in h_i0_frame_D "
        "h_i1_L2_tau_0 h_i1_L2_tau_1 h_i1_L2_tau_2 h_i1_L2_tau_3 "
        "h_i1_L2_tau_4 h_i1_L2_tau_5 h_i1_L2_tau_6 h_i1_L2_tau_7 "
        "h_i1_L2_tau_8 h_i1_L2_tau_9 h_i1_L2_tau_10 "
        "h_i1_L2_not_g "
        "h_i1_L2_frame_n h_i1_L2_frame_i h_i1_L2_frame_k h_i1_L2_frame_D_in "
        "h_i2_trans_i h_i2_frame_n h_i2_frame_j h_i2_frame_k "
        "h_i2_frame_D_in h_i2_frame_D"
    )


def _cite_fw_l1_body_inductive_chain(chosen, hyp_for):
    """sc11 — L0's body around L1 (body inductive). Goal: τ@L0 at s3."""
    return (
        "exact SynthLean.FloydWarshallHelpers.fw_l1_body_inductive_chain "
        "n_s0 i_s0 j_s0 k_s0 D_in_s0 D_s0 "
        "n_s1 i_s1 j_s1 k_s1 D_in_s1 D_s1 "
        "n_s2 i_s2 j_s2 k_s2 D_in_s2 D_s2 "
        "n_s3 i_s3 j_s3 k_s3 D_in_s3 D_s3 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 h_enc_g "
        "h_i0_trans_i h_i0_frame_n h_i0_frame_j h_i0_frame_k "
        "h_i0_frame_D_in h_i0_frame_D "
        "h_i1_L1_tau_0 h_i1_L1_tau_1 h_i1_L1_tau_2 h_i1_L1_tau_3 "
        "h_i1_L1_tau_4 h_i1_L1_tau_5 h_i1_L1_tau_6 "
        "h_i1_L1_not_g "
        "h_i1_L1_frame_n h_i1_L1_frame_k h_i1_L1_frame_D_in "
        "h_i2_trans_k h_i2_frame_n h_i2_frame_i h_i2_frame_j "
        "h_i2_frame_D_in h_i2_frame_D"
    )


def _cite_post_from_inv(chosen, hyp_for):
    """Cite floyd_warshall_post_from_inv for the L0 bundle-post.

    Required τ atoms: k_le_n (orig index 1), outer-table (3).
    Translator emits these as `h_tau_<pos>` in chosen-subset order.

    The chain-bundle translator primes loop-modified vars: `D` and
    `k` become `D'` and `k'` in the emitted theorem (post-loop
    state).  The helper expects the post-loop values, so we pass
    `D' n k'`.  `D_in` is not loop-modified, stays unprimed.
    """
    h_k_le_n = hyp_for("tau@L0", 1)
    h_outer = hyp_for("tau@L0", 3)
    return (
        "exact SynthLean.FloydWarshallHelpers.floyd_warshall_post_from_inv "
        f"D' D_in n k' {h_k_le_n} {h_outer} h_not_g"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.floyd_warshall.Helpers",
    entries=[
    HelperEntry(
        helper_name="floyd_warshall_post_from_inv",
        applies_to=(lambda sc_kind, loop_id, branch_idx:
                    sc_kind == "safety-bundle-post" and loop_id == "L0"),
        required_atoms={
            "tau@L0": frozenset({1, 3}),  # k_le_n + outer-table
        },
        cite=_cite_post_from_inv,
    ),
    # sc4 — L2 inductive branch 0.
    HelperEntry(
        helper_name="fw_l2_inductive_branch_0",
        applies_to=(lambda sc_kind, loop_id, branch_idx:
                    sc_kind == "safety" and loop_id == "L2" and branch_idx == 0),
        required_atoms={
            "tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}),
        },
        cite=_cite_fw_l2_inductive_branch_0,
    ),
    # sc6 — L2 inductive branch 1.
    HelperEntry(
        helper_name="fw_l2_inductive_branch_1",
        applies_to=(lambda sc_kind, loop_id, branch_idx:
                    sc_kind == "safety" and loop_id == "L2" and branch_idx == 1),
        required_atoms={
            "tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}),
        },
        cite=_cite_fw_l2_inductive_branch_1,
    ),
    # sc1 — L1 entry (chain-aware).
    HelperEntry(
        helper_name="fw_l1_entry_chain",
        applies_to=(lambda sc_kind, loop_id, branch_idx:
                    sc_kind == "safety-bundle-entry" and loop_id == "L1"),
        required_atoms={
            "tau@L0": frozenset({0, 1, 2, 3}),
            "tau@L1": frozenset({0, 1, 2, 3, 4, 5, 6}),
        },
        cite=_cite_fw_l1_entry_chain,
    ),
    # sc2 — L2 entry (chain-aware).
    HelperEntry(
        helper_name="fw_l2_entry_chain",
        applies_to=(lambda sc_kind, loop_id, branch_idx:
                    sc_kind == "safety-bundle-entry" and loop_id == "L2"),
        required_atoms={
            "tau@L1": frozenset({0, 1, 2, 3, 4, 5, 6}),
            "tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}),
        },
        cite=_cite_fw_l2_entry_chain,
    ),
    # sc9 — L2 body inductive (L1's body around L2).
    HelperEntry(
        helper_name="fw_l2_body_inductive_chain",
        applies_to=(lambda sc_kind, loop_id, branch_idx:
                    sc_kind == "safety-bundle-post" and loop_id == "L2"),
        required_atoms={
            "tau@L1": frozenset({0, 1, 2, 3, 4, 5, 6}),
            "tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}),
        },
        cite=_cite_fw_l2_body_inductive_chain,
    ),
    # sc11 — L1 body inductive (L0's body around L1).
    HelperEntry(
        helper_name="fw_l1_body_inductive_chain",
        applies_to=(lambda sc_kind, loop_id, branch_idx:
                    sc_kind == "safety-bundle-post" and loop_id == "L1"),
        required_atoms={
            "tau@L0": frozenset({0, 1, 2, 3}),
            "tau@L1": frozenset({0, 1, 2, 3, 4, 5, 6}),
        },
        cite=_cite_fw_l1_body_inductive_chain,
    ),
    ],
)


XFAIL_REASON: str | None = None  # VERIFIED 2026-05-19 (<60s, 1 solution).
# Earlier history:
#   - Atom design landed as a north-star-(3) data point.
#   - sc13 (L0 final post) covered by floyd_warshall_post_from_inv
#     since H.2.CODEGEN.
#   - #167: chain-aware translator support for nested+chained
#     loops + 6 new Tier-2 axioms (sc1, sc2, sc4, sc6, sc9, sc11).
#     Smoke tests confirmed all 7 obligations close ~4.5s via
#     helpers.  Full synth wedged on ranking-lb enumeration.
#   - §H.4: cache-only Lean for ranking-*, cardinality-ordered
#     enum for ranking-* with |τ|≥10, and a general helper
#     short-circuit on the Z3 path.  Together these unblocked
#     FW E2E.  Synthesizes the classical 3-loop DP.


# === Quantified atoms ============================================

# τ_outer: ∀i,j. 0 ≤ i,j < n → D[i][j] == sp(D_in, i, j, k)
_OUTER_TABLE_FILLED = (
    "ForAll(lambda i_, j_: Implies("
    "  0 <= i_ and i_ < n and 0 <= j_ and j_ < n, "
    "  D[i_][j_] == sp(D_in, i_, j_, k)))"
)

# τ_middle: "rows fully updated" + "rows still at k".
_MIDDLE_ROWS_UPDATED = (
    "ForAll(lambda i_, j_: Implies("
    "  0 <= i_ and i_ < i and 0 <= j_ and j_ < n, "
    "  D[i_][j_] == sp(D_in, i_, j_, k + 1)))"
)
_MIDDLE_ROWS_PENDING = (
    "ForAll(lambda i_, j_: Implies("
    "  i <= i_ and i_ < n and 0 <= j_ and j_ < n, "
    "  D[i_][j_] == sp(D_in, i_, j_, k)))"
)

# τ_inner: 4 sub-properties.
_INNER_PRIOR_ROWS = _MIDDLE_ROWS_UPDATED   # same form, rows < i.
_INNER_CURROW_DONE = (
    "ForAll(lambda j_: Implies("
    "  0 <= j_ and j_ < j, "
    "  D[i][j_] == sp(D_in, i, j_, k + 1)))"
)
_INNER_CURROW_PENDING = (
    "ForAll(lambda j_: Implies("
    "  j <= j_ and j_ < n, "
    "  D[i][j_] == sp(D_in, i, j_, k)))"
)
_INNER_FUTURE_ROWS = (
    "ForAll(lambda i_, j_: Implies("
    "  i + 1 <= i_ and i_ < n and 0 <= j_ and j_ < n, "
    "  D[i_][j_] == sp(D_in, i_, j_, k)))"
)


PROBLEM = Problem(
    description = (
        "Given an n×n integer matrix D_in (initial distances, "
        "D_in[i][i] == 0 and D_in[i][j] = direct edge weight "
        "otherwise), compute all-pairs shortest paths in place "
        "via Floyd-Warshall."
    ),

    template = (
        SB()
        >> Loop(
            SB()
            >> Loop(
                SB()
                >> Loop(SB(n=2))
                >> SB()
            )
            >> SB()
        )
    ),
    inputs   = [Var("D_in", "int[][]", "input"),
                Var("n", "int", "input"),
                Var("D", "int[][]", "input")],
    outputs  = [Var("D", "int[][]", "output")],
    locals   = [Var("i", "int", "local"),
                Var("j", "int", "local"),
                Var("k", "int", "local")],

    pre = (
        "n >= 0 and "
        "ForAll(lambda i_, j_: Implies("
        "  0 <= i_ and i_ < n and 0 <= j_ and j_ < n, "
        "  D[i_][j_] == D_in[i_][j_])) and "
        # Non-negative-cycles assumption: paths from a vertex
        # to itself through any intermediate subset must be
        # non-negative.  Matches the Lean-side `sp_self_nonneg`
        # axiom — the one fundamental trust point of FW
        # correctness.
        "ForAll(lambda k_: Implies(k_ >= 0, sp(D_in, k_, k_, k_) >= 0))"
    ),
    post = (
        "ForAll(lambda i_, j_: Implies("
        "  0 <= i_ and i_ < n and 0 <= j_ and j_ < n, "
        "  D[i_][j_] == sp(D_in, i_, j_, n)))"
    ),

    uninterpreted = [
        # sp takes the D_in array snapshot + indices + level.
        ("sp", ["int[][]", "int", "int", "int"], "int"),
    ],
    axioms = [
        # Base case at k = 0: sp matches the input matrix.
        ("ForAll(lambda i_, j_: "
         " sp(D_in, i_, j_, 0) == D_in[i_][j_])"),
        # Recurrence: sp at level k+1 picks the min of the
        # k-level direct or via-k path.
        ("ForAll(lambda i_, j_, k_: Implies(k_ >= 0, "
         " sp(D_in, i_, j_, k_ + 1) == "
         "  (sp(D_in, i_, j_, k_) "
         "   if sp(D_in, i_, j_, k_) <= "
         "      sp(D_in, i_, k_, k_) + sp(D_in, k_, j_, k_) "
         "   else sp(D_in, i_, k_, k_) + sp(D_in, k_, j_, k_))))"),
    ],

    atoms = {
        # Phase 1: SB init.  k := 0.
        "s@B0": [{"k": "0"}],

        # Phase 2: outer Loop.  while k < n.
        "tau@L0": [
            "0 <= k", "k <= n", "n >= 0",
            _OUTER_TABLE_FILLED,
        ],
        "g@L0":   ["k < n"],
        "phi@L0": ["n - k"],

        # Phase 2.1: inner SB.  i := 0.
        "s@B1": [{"i": "0"}],

        # Phase 2.2: middle Loop.  while i < n.
        "tau@L1": [
            "0 <= k", "k < n", "0 <= i", "i <= n", "n >= 0",
            _MIDDLE_ROWS_UPDATED,
            _MIDDLE_ROWS_PENDING,
        ],
        "g@L1":   ["i < n"],
        "phi@L1": ["n - i"],

        # Phase 2.2.1: innermost SB.  j := 0.
        "s@B2": [{"j": "0"}],

        # Phase 2.2.2: inner Loop.  while j < n.  Body = SB(n=2).
        "tau@L2": [
            "0 <= k", "k < n", "0 <= i", "i < n",
            "0 <= j", "j <= n", "n >= 0",
            _INNER_PRIOR_ROWS,
            _INNER_CURROW_DONE,
            _INNER_CURROW_PENDING,
            _INNER_FUTURE_ROWS,
        ],
        "g@L2":   ["j < n"],
        "phi@L2": ["n - j"],

        # SB(n=2) branches: D[i][j] ≤ D[i][k] + D[k][j] keeps it;
        # else updates to D[i][k] + D[k][j].
        "g@B3.0": ["D[i][j] <= D[i][k] + D[k][j]"],
        "s@B3.0": [{"j": "j + 1"}],
        "g@B3.1": ["D[i][j] > D[i][k] + D[k][j]"],
        "s@B3.1": [
            {"D": "Update(D, i, j, D[i][k] + D[k][j])",
             "j": "j + 1"}
        ],

        # Phase 2.2.3: post-inner SB.  i := i + 1.
        "s@B4": [{"i": "i + 1"}],

        # Phase 2.3: post-middle SB.  k := k + 1.
        "s@B5": [{"k": "k + 1"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    solver_timeout_ms = 3_600_000,  # 60 min — triple-nested
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/floyd_warshall",
    helper_registry = _HELPER_REGISTRY,
)


if __name__ == "__main__":
    print(f"floyd_warshall — XFAIL_REASON: {XFAIL_REASON!r}")
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1 if XFAIL_REASON is None else 0)
    print(f"Found {len(result.solutions)} solution(s).")
    for n_, sol in enumerate(result.solutions):
        print(f"── solution #{n_} (score={sol.score:g}) ──")
        print(sol.code)
        print()
