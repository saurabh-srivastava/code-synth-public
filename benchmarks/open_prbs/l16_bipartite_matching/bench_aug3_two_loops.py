"""bench_aug3_two_loops — C1.D K.3.2 step-up: 2-nested-loop AP search.

Given an unmatched vertex `u` as input, search the bipartite graph
for a length-3 augmenting path `u-v-z-w` and set a `found` flag.
DOES NOT flip M — keeps the matching unchanged.  The point of this
benchmark is to validate the found-flag-with-outer-guard idiom in
a 2-nested-loop setting, before adding the flip (which raises
matching-invariant proof obligations) and a 3rd outer loop.

Algorithm:

  found := 0
  v := -1
  while v + 1 < n and found == 0:
      v := v + 1
      w := 0
      while w < n:
          if (v != u and G[u][v] >= 1 and M[v] != -1
              and w != u and w != v and w != M[v]
              and M[w] == -1 and G[M[v]][w] >= 1):
              found := 1
              break
          w := w + 1

Post: M unchanged; found ∈ {0, 1}.

Why this is the next step after the baby step:
  - Baby step: 1 loop with break, u/v/z all inputs.
  - This: 2 loops, only u input; v iterated by outer, w iterated
    by inner.  Validates that outer-guard `found == 0` correctly
    short-circuits after inner break.
  - The flip is omitted to isolate the search/break/found-flag
    structure from matching-invariant proof complexity.  A
    follow-up benchmark adds the flip (needs Tier-3 helper for
    MI preservation).

Template uses the "increment-at-start" idiom so the inner Loop is
the LAST item in outer's body chain (no chain tail after inner,
which would need K.D.2.a).
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


def _cite_inner_entry(chosen, hyp_for):
    """sc1 — L1 entry-bundle.  Cite the K.3.2 2-loop inner entry
    helper with full τ_L0 (4 atoms) and the framework-emitted
    B1 trans/frame hypotheses."""
    return (
        "exact SynthLean.Y2Corpus.L16Aug3TwoLoops.k32_2l_inner_entry "
        "n_s0 u_s0 found_s0 v_s0 w_s0 M_s0 G_s0 "
        "n_s1 u_s1 found_s1 v_s1 w_s1 M_s1 G_s1 "
        "h_pre.1 h_pre.2.1 h_pre.2.2.1 h_pre.2.2.2.1 "
        "h_pre.2.2.2.2.1 h_pre.2.2.2.2.2 "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_g "
        "h_i0_trans_v h_i0_trans_w "
        "h_i0_frame_n h_i0_frame_u h_i0_frame_found "
        "h_i0_frame_M h_i0_frame_G"
    )


def _cite_inner_break(chosen, hyp_for):
    """sc3 — L1 inner break-bundle (branch_idx=0).  Cite the
    K.3.2 2-loop inner break helper with full τ_L1 (5 atoms);
    consequent is τ_L0 (4 atoms) at body_out."""
    return (
        "exact SynthLean.Y2Corpus.L16Aug3TwoLoops.k32_2l_inner_break "
        "n u found v w M G found' "
        "h_pre.1 h_pre.2.1 h_pre.2.2.1 h_pre.2.2.2.1 "
        "h_pre.2.2.2.2.1 h_pre.2.2.2.2.2 "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 "
        "h_guard h_trans_found"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.l16_aug3_two_loops.Helpers",
    entries=[
        HelperEntry(
            helper_name="k32_2l_inner_entry",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-entry"
                        and loop_id == "L1"),
            required_atoms={
                "tau@L0": frozenset({0, 1, 2, 3}),
            },
            cite=_cite_inner_entry,
        ),
        HelperEntry(
            helper_name="k32_2l_inner_break",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post"
                        and loop_id == "L1"
                        and branch_idx == 0),
            required_atoms={
                "tau@L1": frozenset({0, 1, 2, 3, 4}),
            },
            cite=_cite_inner_break,
        ),
        HelperEntry(
            helper_name="k32_2l_outer_body_inductive",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post"
                        and loop_id == "L1"
                        and branch_idx is None),
            required_atoms={
                "tau@L0": frozenset({0, 1, 2, 3}),
                "tau@L1": frozenset({0, 1, 2, 3, 4}),
            },
            cite=(lambda chosen, hyp_for:
                  "exact SynthLean.Y2Corpus.L16Aug3TwoLoops.k32_2l_outer_body_inductive "
                  "n_s0 u_s0 found_s0 v_s0 w_s0 M_s0 G_s0 "
                  "n_s1 u_s1 found_s1 v_s1 w_s1 M_s1 G_s1 "
                  "n_s2 u_s2 found_s2 v_s2 w_s2 M_s2 G_s2 "
                  "h_pre.1 h_pre.2.1 h_pre.2.2.1 h_pre.2.2.2.1 "
                  "h_pre.2.2.2.2.1 h_pre.2.2.2.2.2 "
                  "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
                  "h_enc_g "
                  "h_i0_trans_v h_i0_trans_w "
                  "h_i0_frame_n h_i0_frame_u h_i0_frame_found "
                  "h_i0_frame_M h_i0_frame_G "
                  "h_i1_L1_tau_0 h_i1_L1_tau_1 h_i1_L1_tau_2 "
                  "h_i1_L1_tau_3 h_i1_L1_tau_4 "
                  "h_i1_L1_frame_n h_i1_L1_frame_u h_i1_L1_frame_v "
                  "h_i1_L1_frame_M h_i1_L1_frame_G"),
        ),
    ],
)


PROBLEM = Problem(
    template = (
        SB() >> Loop(SB() >> Loop(SB(n=2))) >> SB()
    ),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input"),
                Var("u", "int",   "input")],
    outputs  = [Var("M",     "int[]", "output"),
                Var("found", "int",   "output")],
    locals   = [Var("v", "int", "local"),
                Var("w", "int", "local")],

    # Dummy axiom triggers axiom-heavy Lean routing (lesson #65).
    axioms = ["0 == 0"],

    pre  = (
        "n >= 0 and "
        "0 <= u and u < n and "
        # M is a valid matching.
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        # u is unmatched.
        "M[u] == -1 and "
        # G symmetric.
        "ForAll(lambda p, q: Implies("
        "0 <= p and p < n and 0 <= q and q < n, "
        "G[p][q] == G[q][p]))"
    ),
    post = (
        # MI preserved (M is unchanged — search-only).
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        "(found == 0 or found == 1)"
    ),

    atoms = {
        # B0 — init: v := -1, w := 0, found := 0.  M unchanged.
        "s@B0": [{"v": "0 - 1", "w": "0", "found": "0"}],

        # Outer L0 invariant — v in [-1, n - 1] (so v+1 ≤ n),
        # MI(M) preserved, found ∈ {0, 1}.  Fpre is propagated
        # into the recursive walk by the framework, so we don't
        # need to carry `n ≥ 0`, `0 ≤ u`, `u < n`, etc.
        "tau@L0": [
            "0 - 1 <= v",
            "v <= n - 1",
            "found == 0 or found == 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
        ],
        # Outer guard short-circuits when found is set.
        "g@L0":   ["v + 1 < n and found == 0"],
        "phi@L0": ["n - 1 - v"],

        # B1 — step v, reset w.  Inner Loop will be last in outer
        # body, so no chain-tail issue.
        "s@B1": [{"v": "v + 1", "w": "0"}],

        # Inner L1 invariant — w in [0, n], MI(M) carried, plus
        # the v range needed at this scope (after B1 increment,
        # v ∈ [0, n-1]).  Fpre is propagated.
        "tau@L1": [
            "w <= n",
            "0 <= v",
            "v <= n - 1",
            "found == 0 or found == 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
        ],
        "g@L1":   ["w < n"],
        "phi@L1": ["n - w"],

        # Inner branch 0: AP found.  Set found := 1, break.  M
        # unchanged (no flip in this benchmark).
        "g@B2.0": [(
            "v != u and G[u][v] >= 1 and M[v] != -1 and "
            "w != u and w != v and w != M[v] and "
            "M[w] == -1 and G[M[v]][w] >= 1"
        )],
        "s@B2.0": [{"found": "1", "_break": True}],

        # Inner branch 1: not a valid AP, advance w.
        "g@B2.1": [(
            "not (v != u and G[u][v] >= 1 and M[v] != -1 and "
            "w != u and w != v and w != M[v] and "
            "M[w] == -1 and G[M[v]][w] >= 1)"
        )],
        "s@B2.1": [{"w": "w + 1"}],

        # B3 — final: preserve all vars.
        "s@B3": [{}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_aug3_two_loops"
    ),
    helper_registry = _HELPER_REGISTRY,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    elapsed = time.monotonic() - t
    print(f"wall: {elapsed:.1f}s")
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for k, sol in enumerate(result.solutions[:1]):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
