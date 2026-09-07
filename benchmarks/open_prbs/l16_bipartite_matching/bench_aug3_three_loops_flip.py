"""bench_aug3_three_loops_flip — C1.D Slice 2.A: 3-nested AP
search WITH the augmenting-path flip applied to M.

Same control flow as bench_aug3_three_loops.py, but the inner
break branch ACTUALLY flips M via a 4-point Update chain.
This proves that MI is preserved through the flip — a non-
trivial case-split since M is now modified by the algorithm.

The flip (parallel-dict; all RHS reference OLD M):
  M[u]    := v
  M[v]    := u
  M[M[v]] := w     (= M[z], assigning to the OLD z)
  M[w]    := M[v]  (= z, the OLD M[v])

Algorithm (synthesized target):

  u, v, w, found := -1, -1, 0, 0
  while (u + 1 < n and found == 0):
      u, v := u + 1, -1
      while (v + 1 < n and found == 0):
          v, w := v + 1, 0
          while (w < n):
              if (v != u and G[u][v] >= 1 and M[v] != -1 and
                  w != u and w != v and w != M[v] and
                  M[w] == -1 and G[M[v]][w] >= 1 and M[u] == -1):
                  found := 1
                  break
              else:
                  w := w + 1
  return M, found

The "increment-at-start" pattern keeps each inner Loop as the
LAST item in its enclosing body chain (no chain-tail after the
inner Loop), so the break's `τ_enclosing(body_out)` consequent
is exact.

Post: M unchanged (search-only, no flip); MI carried through.
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


# Helpers wired iteratively as the wedge-detector surfaces them.
# Each helper closes via omega + direct hypothesis citations
# (algorithm doesn't modify M; MI carried by frame eqs).


_MODULE = "SynthLean.Y2Corpus.L16Aug3ThreeLoopsFlip"


def _pre_hyps():
    return ("h_pre.1 h_pre.2.1 h_pre.2.2")


def _cite_middle_entry(chosen, hyp_for):
    return (
        f"exact {_MODULE}.k32_3lf_middle_entry "
        "n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0 "
        "n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1 "
        + _pre_hyps() + " "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_g "
        "h_i0_trans_u h_i0_trans_v "
        "h_i0_frame_n h_i0_frame_found h_i0_frame_w "
        "h_i0_frame_M h_i0_frame_G"
    )


def _cite_inner_entry(chosen, hyp_for):
    return (
        f"exact {_MODULE}.k32_3lf_inner_entry "
        "n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0 "
        "n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1 "
        + _pre_hyps() + " "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 "
        "h_enc_g "
        "h_i0_trans_v h_i0_trans_w "
        "h_i0_frame_n h_i0_frame_found h_i0_frame_u "
        "h_i0_frame_M h_i0_frame_G"
    )


def _cite_inner_break(chosen, hyp_for):
    # AP-flip version: cite carries `M'` (new M) + `h_trans_M`.
    return (
        f"exact {_MODULE}.k32_3lf_inner_break "
        "n found u v w M G found' M' "
        + _pre_hyps() + " "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 h_tau_7 "
        "h_guard h_trans_M h_trans_found"
    )


def _cite_middle_body(chosen, hyp_for):
    # L2 abstract no longer has h_i1_L2_frame_M (L2 modifies M).
    return (
        f"exact {_MODULE}.k32_3lf_middle_body_ind "
        "n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0 "
        "n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1 "
        "n_s2 found_s2 u_s2 v_s2 w_s2 M_s2 G_s2 "
        + _pre_hyps() + " "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 "
        "h_enc_g "
        "h_i0_trans_v h_i0_trans_w "
        "h_i0_frame_n h_i0_frame_found h_i0_frame_u "
        "h_i0_frame_M h_i0_frame_G "
        "h_i1_L2_tau_0 h_i1_L2_tau_1 h_i1_L2_tau_2 h_i1_L2_tau_3 "
        "h_i1_L2_tau_4 h_i1_L2_tau_5 h_i1_L2_tau_6 h_i1_L2_tau_7 "
        "h_i1_L2_frame_n h_i1_L2_frame_u h_i1_L2_frame_v "
        "h_i1_L2_frame_G"
    )


def _cite_outer_body(chosen, hyp_for):
    # L1 abstract no longer has h_i1_L1_frame_M (L1's body modifies M).
    return (
        f"exact {_MODULE}.k32_3lf_outer_body_ind "
        "n_s0 found_s0 u_s0 v_s0 w_s0 M_s0 G_s0 "
        "n_s1 found_s1 u_s1 v_s1 w_s1 M_s1 G_s1 "
        "n_s2 found_s2 u_s2 v_s2 w_s2 M_s2 G_s2 "
        + _pre_hyps() + " "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_g "
        "h_i0_trans_u h_i0_trans_v "
        "h_i0_frame_n h_i0_frame_found h_i0_frame_w "
        "h_i0_frame_M h_i0_frame_G "
        "h_i1_L1_tau_0 h_i1_L1_tau_1 h_i1_L1_tau_2 h_i1_L1_tau_3 "
        "h_i1_L1_tau_4 h_i1_L1_tau_5 "
        "h_i1_L1_not_g "
        "h_i1_L1_frame_n h_i1_L1_frame_u "
        "h_i1_L1_frame_G"
    )


def _cite_final(chosen, hyp_for):
    # FLAT shape, with M' (since L0 modifies M).
    return (
        f"exact {_MODULE}.k32_3lf_final "
        "n u v w found M G u' v' w' found' M' "
        + _pre_hyps() + " "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_not_g"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.l16_aug3_three_loops_flip.Helpers",
    entries=[
        # sc1: L1 entry-bundle.
        HelperEntry(
            helper_name="k32_3lf_middle_entry",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-entry"
                        and loop_id == "L1"),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3})},
            cite=_cite_middle_entry,
        ),
        # sc2: L2 entry-bundle.
        HelperEntry(
            helper_name="k32_3lf_inner_entry",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-entry"
                        and loop_id == "L2"),
            required_atoms={"tau@L1": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_inner_entry,
        ),
        # sc4: L2 inner break with FLIP.  τ_L2 now 8 atoms.
        HelperEntry(
            helper_name="k32_3lf_inner_break",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post"
                        and loop_id == "L2"
                        and branch_idx == 0),
            required_atoms={
                "tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7}),
            },
            cite=_cite_inner_break,
        ),
        # sc8: L1 chain-bundle-post (middle body inductive).
        HelperEntry(
            helper_name="k32_3lf_middle_body_ind",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post"
                        and loop_id == "L2"
                        and branch_idx is None),
            required_atoms={
                "tau@L1": frozenset({0, 1, 2, 3, 4, 5}),
                "tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7}),
            },
            cite=_cite_middle_body,
        ),
        # sc10: L0 chain-bundle-post (outer body inductive).
        HelperEntry(
            helper_name="k32_3lf_outer_body_ind",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post"
                        and loop_id == "L1"
                        and branch_idx is None),
            required_atoms={
                "tau@L0": frozenset({0, 1, 2, 3}),
                "tau@L1": frozenset({0, 1, 2, 3, 4, 5}),
            },
            cite=_cite_outer_body,
        ),
        # sc12: L0 final bundle ⇒ post.
        HelperEntry(
            helper_name="k32_3lf_final",
            applies_to=(lambda sc_kind, loop_id, branch_idx:
                        sc_kind == "safety-bundle-post"
                        and loop_id == "L0"
                        and branch_idx is None),
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3})},
            cite=_cite_final,
        ),
    ],
)


PROBLEM = Problem(
    template = (
        SB()
        >> Loop(SB() >> Loop(SB() >> Loop(SB(n=2))))
        >> SB()
    ),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input")],
    outputs  = [Var("M",     "int[]", "output"),
                Var("found", "int",   "output")],
    locals   = [Var("u", "int", "local"),
                Var("v", "int", "local"),
                Var("w", "int", "local")],

    # Dummy axiom triggers axiom-heavy Lean routing (lesson #65).
    axioms = ["0 == 0"],

    pre  = (
        "n >= 0 and "
        # M is a valid matching.
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        # G symmetric.
        "ForAll(lambda p, q: Implies("
        "0 <= p and p < n and 0 <= q and q < n, "
        "G[p][q] == G[q][p]))"
    ),
    post = (
        # MI preserved (M unchanged — search-only).
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        "(found == 0 or found == 1)"
    ),

    atoms = {
        # B0 — init: u := -1, v := -1, w := 0, found := 0.
        "s@B0": [{"u": "0 - 1", "v": "0 - 1", "w": "0", "found": "0"}],

        # Outer L0 invariant — u in [-1, n - 1], MI, found.
        "tau@L0": [
            "0 - 1 <= u",
            "u <= n - 1",
            "found == 0 or found == 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
        ],
        "g@L0":   ["u + 1 < n and found == 0"],
        "phi@L0": ["n - 1 - u"],

        # B1 — step u, reset v.  Inner Loop will follow; no chain
        # tail after it.
        "s@B1": [{"u": "u + 1", "v": "0 - 1"}],

        # Middle L1 invariant — v in [-1, n-1], u in [0, n-1].
        "tau@L1": [
            "0 - 1 <= v",
            "v <= n - 1",
            "0 <= u",
            "u <= n - 1",
            "found == 0 or found == 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
        ],
        "g@L1":   ["v + 1 < n and found == 0"],
        "phi@L1": ["n - 1 - v"],

        # B2 — step v, reset w.  Inner Loop L2 follows.
        "s@B2": [{"v": "v + 1", "w": "0"}],

        # Inner L2 invariant — w in [0, n], plus carried v, u.
        # `0 <= w` (atom 7, appended) is load-bearing for the
        # AP-flip MI proof: at index `M v`, new_M[M v] = w, so
        # we need both `0 <= w` and `w < n` to conclude w ∈ [0, n).
        "tau@L2": [
            "w <= n",
            "0 <= v",
            "v <= n - 1",
            "0 <= u",
            "u <= n - 1",
            "found == 0 or found == 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
            "0 <= w",
        ],
        "g@L2":   ["w < n"],
        "phi@L2": ["n - w"],

        # Inner branch 0: AP found.  Flip M via 4-point Update
        # chain, set found, break.  RHS refers to OLD M
        # (parallel-dict).
        "g@B3.0": [(
            "v != u and G[u][v] >= 1 and M[v] != -1 and "
            "w != u and w != v and w != M[v] and "
            "M[w] == -1 and G[M[v]][w] >= 1 and M[u] == -1"
        )],
        "s@B3.0": [{
            "M": ("Update(Update(Update(Update(M, u, v), v, u), "
                  "M[v], w), w, M[v])"),
            "found": "1",
            "_break": True,
        }],

        # Inner branch 1: not a valid AP, advance w.
        "g@B3.1": [(
            "not (v != u and G[u][v] >= 1 and M[v] != -1 and "
            "w != u and w != v and w != M[v] and "
            "M[w] == -1 and G[M[v]][w] >= 1 and M[u] == -1)"
        )],
        "s@B3.1": [{"w": "w + 1"}],

        # B4 — final: preserve all.
        "s@B4": [{}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 3_600_000,   # 60 min budget — heavy benchmark
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_aug3_three_loops_flip"
    ),
    helper_registry = _HELPER_REGISTRY,
    # Default wedge_threshold (30) is fine.
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
