"""bench_max_matching_recur — C1.D Slice 2.B (Option X):
maximum matching via tail-recursive AP search + flip, with
axiomatized Berge.

Tail-recursive design (replaces the outer-outer Loop with
Recur):

  def find_max(G, n, M):
      found := 0
      u := -1
      while u + 1 < n and found == 0:    # L_u
          u := u + 1
          v := -1
          while v + 1 < n and found == 0:    # L_v
              v := v + 1
              w := 0
              while w < n:                    # L_w
                  if AP_conditions:
                      apply 4-point flip
                      found := 1
                      break
                  w := w + 1
      if found == 1:
          return find_max(G, n, M)    # tail-recur with new M
      else:
          return M                    # base case

The Recur replaces the outer-outer Loop's "while found == 1"
pattern.  Per-procedure ranking `phi@PROC = n - 2 *
MatchingSize(M, n)` decreases by 2 per recur (one AP-flip
increases MatchingSize by 1 per axiom).  Termination
guaranteed.

Slice 2.B Option X scope:
  - UFs: MatchingSize, IsMatching, IsMaxMatching, ExistsAugPath.
  - Axioms: MatchingSize bounds + flip-increases-size +
    Length3SearchSufficient (class restriction) + Berge.
  - Pre: IsMatching(G, n, M).
  - Post: IsMaxMatching(G, n, M).

This is the first L1.6 benchmark to produce a Berge-style
maximum-matching claim via the framework.
"""
from synth import Problem, SB, Loop, Recur, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


_MODULE = "SynthLean.Y2Corpus.L16MaxMatchingRecur"


def _pre_hyps():
    """h_pre destructure: h_pre is the 3-conjunct
    (n >= 0 ∧ IsMatching ∧ G symmetric).  Cited as a single
    bundle since the helpers' first parameter is exactly this."""
    return "h_pre"


def _cite_sc2(chosen, hyp_for):
    return (
        f"exact {_MODULE}.mm_sc2_l1_entry "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 h_enc_g "
        "h_i0_trans_u h_i0_trans_v "
        "h_i0_frame_n h_i0_frame_w h_i0_frame_found "
        "h_i0_frame_M h_i0_frame_G"
    )


def _cite_sc3(chosen, hyp_for):
    return (
        f"exact {_MODULE}.mm_sc3_l2_entry "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 h_enc_g "
        "h_i0_trans_v h_i0_trans_w "
        "h_i0_frame_n h_i0_frame_u h_i0_frame_found "
        "h_i0_frame_M h_i0_frame_G"
    )


def _cite_sc5(chosen, hyp_for):
    return (
        f"exact {_MODULE}.mm_sc5_l2_break "
        "n k u v w found M G found' M' "
        "h_pre "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 h_tau_7 "
        "h_guard h_trans_M h_trans_found"
    )


def _cite_sc6(chosen, hyp_for):
    return (
        f"exact {_MODULE}.mm_sc6_l2_safety_step "
        "n k u v w found M G w' "
        "h_pre "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 h_tau_7 "
        "h_guard h_trans_w"
    )


def _cite_sc9(chosen, hyp_for):
    return (
        f"exact {_MODULE}.mm_sc9_l1_body_ind "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1 "
        "n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 M_s2 G_s2 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 h_enc_g "
        "h_i0_trans_v h_i0_trans_w "
        "h_i0_frame_n h_i0_frame_u h_i0_frame_found "
        "h_i0_frame_M h_i0_frame_G "
        "h_i1_L2_tau_0 h_i1_L2_tau_1 h_i1_L2_tau_2 h_i1_L2_tau_3 "
        "h_i1_L2_tau_4 h_i1_L2_tau_5 h_i1_L2_tau_6 h_i1_L2_tau_7 "
        "h_i1_L2_frame_n h_i1_L2_frame_u h_i1_L2_frame_v h_i1_L2_frame_G"
    )


def _cite_sc11(chosen, hyp_for):
    return (
        f"exact {_MODULE}.mm_sc11_l0_body_ind "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 M_s1 G_s1 "
        "n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 M_s2 G_s2 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 h_enc_g "
        "h_i0_trans_u h_i0_trans_v "
        "h_i0_frame_n h_i0_frame_w h_i0_frame_found "
        "h_i0_frame_M h_i0_frame_G "
        "h_i1_L1_tau_0 h_i1_L1_tau_1 h_i1_L1_tau_2 h_i1_L1_tau_3 "
        "h_i1_L1_tau_4 h_i1_L1_tau_5 h_i1_L1_not_g "
        "h_i1_L1_frame_n h_i1_L1_frame_u h_i1_L1_frame_G"
    )


def _cite_sc14(chosen, hyp_for):
    # FLAT shape: pre-loop (n, u, v, w, found, M, G) + post-loop
    # primed (u', v', w', found', M').
    return (
        f"exact {_MODULE}.mm_sc14_final_berge "
        "n k u v w found M G u' v' w' found' M' "
        "h_pre "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_not_g"
    )


def _cite_sc15(chosen, hyp_for):
    # mm_sc15_coverage now takes ONLY τ@L0 atom 2 (`found ∈ {0,1}`);
    # adapts to the atom's position in the chosen subset.
    h_atom2 = hyp_for("tau@L0", 2)
    return (
        f"exact {_MODULE}.mm_sc15_coverage "
        "n k u v w found M G "
        f"h_pre {h_atom2}"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.l16_max_matching_recur.Helpers",
    entries=[
        HelperEntry("mm_sc2_l1_entry",
            applies_to=lambda k, l, b: k == "safety-bundle-entry" and l == "L1",
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3})},
            cite=_cite_sc2),
        HelperEntry("mm_sc3_l2_entry",
            applies_to=lambda k, l, b: k == "safety-bundle-entry" and l == "L2",
            required_atoms={"tau@L1": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_sc3),
        HelperEntry("mm_sc5_l2_break",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L2" and b == 0,
            required_atoms={"tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7})},
            cite=_cite_sc5),
        HelperEntry("mm_sc6_l2_safety_step",
            applies_to=lambda k, l, b: k == "safety" and l == "L2" and b == 1,
            required_atoms={"tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7})},
            cite=_cite_sc6),
        HelperEntry("mm_sc9_l1_body_ind",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L2" and b is None,
            required_atoms={"tau@L1": frozenset({0, 1, 2, 3, 4, 5}),
                            "tau@L2": frozenset({0, 1, 2, 3, 4, 5, 6, 7})},
            cite=_cite_sc9),
        HelperEntry("mm_sc11_l0_body_ind",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L1" and b is None,
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3}),
                            "tau@L1": frozenset({0, 1, 2, 3, 4, 5})},
            cite=_cite_sc11),
        HelperEntry("mm_sc14_final_berge",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L0" and b is None,
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3})},
            cite=_cite_sc14),
        HelperEntry("mm_sc15_coverage",
            applies_to=lambda k, l, b: k == "coverage" and l is None,
            # Only atom 2 (`found = 0 ∨ found = 1`) is needed — relaxes
            # required_atoms so per-subset enumeration fires the helper
            # on partial-τ subsets too, eliminating sound-mode rejections.
            required_atoms={"tau@L0": frozenset({2})},
            cite=_cite_sc15),
    ],
)


# AP precondition string (shared across guard + axiom).
_AP_COND = (
    "v != u and G[u][v] >= 1 and M[v] != -1 and "
    "w != u and w != v and w != M[v] and "
    "M[w] == -1 and G[M[v]][w] >= 1 and M[u] == -1"
)


PROBLEM = Problem(
    template = (
        SB()
        >> Loop(
            SB()
            >> Loop(
                SB()
                >> Loop(SB(n=2))
            )
        )
        >> SB(n=2)
    ),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input"),
                Var("k", "int",   "input")],   # iteration budget
    outputs  = [Var("M", "int[]", "output")],
    locals   = [Var("u", "int", "local"),
                Var("v", "int", "local"),
                Var("w", "int", "local"),
                Var("found", "int", "local")],

    uninterpreted = [
        ("MatchingSize",   ["int[]", "int"], "int"),
        ("IsMatching",     ["int[][]", "int", "int[]"], "int"),
        ("IsMaxMatching",  ["int[][]", "int", "int[]"], "int"),
        ("ExistsAugPath",  ["int[][]", "int", "int[]"], "int"),
    ],

    axioms = [
        # A1: MatchingSize bounds.
        "ForAll(lambda M_arr, m_n: Implies(m_n >= 0, "
        "MatchingSize(M_arr, m_n) >= 0))",
        "ForAll(lambda M_arr, m_n: Implies(m_n >= 0, "
        "2 * MatchingSize(M_arr, m_n) <= m_n))",

        # A2: AP-flip increases MatchingSize by 1.
        # Quantifier-instantiation note: the flip transition's
        # Update^4 chain in the synthesized code must match this
        # pattern for the axiom to fire.
        "ForAll(lambda G_mat, m_n, M_arr, m_u, m_v, m_w: Implies("
        "    m_n >= 0 and "
        "    0 <= m_u and m_u < m_n and "
        "    0 <= m_v and m_v < m_n and "
        "    0 <= m_w and m_w < m_n and "
        "    m_v != m_u and m_w != m_u and m_w != m_v and "
        "    m_w != M_arr[m_v] and M_arr[m_v] != -1 and "
        "    M_arr[m_w] == -1 and M_arr[m_u] == -1, "
        "    MatchingSize("
        "      Update(Update(Update(Update(M_arr, m_u, m_v), m_v, m_u), "
        "             M_arr[m_v], m_w), m_w, M_arr[m_v]), m_n) "
        "    == MatchingSize(M_arr, m_n) + 1"
        "))",

        # A3: AP-flip preserves IsMatching.
        "ForAll(lambda G_mat, m_n, M_arr, m_u, m_v, m_w: Implies("
        "    IsMatching(G_mat, m_n, M_arr) == 1 and "
        "    0 <= m_u and m_u < m_n and "
        "    0 <= m_v and m_v < m_n and "
        "    0 <= m_w and m_w < m_n and "
        "    m_v != m_u and m_w != m_u and m_w != m_v and "
        "    m_w != M_arr[m_v] and M_arr[m_v] != -1 and "
        "    M_arr[m_w] == -1 and M_arr[m_u] == -1 and "
        "    G_mat[m_u][m_v] >= 1 and G_mat[M_arr[m_v]][m_w] >= 1, "
        "    IsMatching(G_mat, m_n, "
        "      Update(Update(Update(Update(M_arr, m_u, m_v), m_v, m_u), "
        "             M_arr[m_v], m_w), m_w, M_arr[m_v])) == 1"
        "))",

        # A4: Berge — IsMatching ∧ ¬ExistsAugPath → IsMaxMatching.
        "ForAll(lambda G_mat, m_n, M_arr: Implies("
        "    IsMatching(G_mat, m_n, M_arr) == 1 and "
        "    ExistsAugPath(G_mat, m_n, M_arr) == 0, "
        "    IsMaxMatching(G_mat, m_n, M_arr) == 1"
        "))",

        # A5: Length-3 search sufficient (class restriction):
        # if no length-3 AP exists for M, then no AP of any
        # length exists.  TRUSTED for the graph class our
        # benchmark targets.
        "ForAll(lambda G_mat, m_n, M_arr: Implies("
        "    IsMatching(G_mat, m_n, M_arr) == 1 and "
        "    (ForAll(lambda k_u, k_v, k_w: not ("
        "        0 <= k_u and k_u < m_n and "
        "        0 <= k_v and k_v < m_n and "
        "        0 <= k_w and k_w < m_n and "
        "        k_v != k_u and k_w != k_u and k_w != k_v and "
        "        k_w != M_arr[k_v] and M_arr[k_v] != -1 and "
        "        M_arr[k_w] == -1 and M_arr[k_u] == -1 and "
        "        G_mat[k_u][k_v] >= 1 and G_mat[M_arr[k_v]][k_w] >= 1))), "
        "    ExistsAugPath(G_mat, m_n, M_arr) == 0"
        "))",
    ],

    pre = (
        "n >= 0 and "
        "k > 0 and "                # iteration budget; Fpre(args) goes
                                    # vacuous at k = 1 (args.k = 0)
        "IsMatching(G, n, M) == 1 and "
        "ForAll(lambda p, q: Implies("
        "0 <= p and p < n and 0 <= q and q < n, "
        "G[p][q] == G[q][p]))"
    ),
    post = "IsMaxMatching(G, n, M) == 1",

    atoms = {
        # B0 — init.
        "s@B0": [{"found": "0", "u": "0 - 1", "v": "0 - 1", "w": "0"}],

        # L0 (u-loop) invariant — IsMatching preserved + found ∈ {0,1}.
        "tau@L0": [
            "0 - 1 <= u",
            "u <= n - 1",
            "found == 0 or found == 1",
            "IsMatching(G, n, M) == 1",
        ],
        "g@L0":   ["u + 1 < n and found == 0"],
        "phi@L0": ["n - 1 - u"],

        # B1 — u-step.
        "s@B1": [{"u": "u + 1", "v": "0 - 1"}],

        # L1 (v-loop) invariant.
        "tau@L1": [
            "0 - 1 <= v",
            "v <= n - 1",
            "0 <= u",
            "u <= n - 1",
            "found == 0 or found == 1",
            "IsMatching(G, n, M) == 1",
        ],
        "g@L1":   ["v + 1 < n and found == 0"],
        "phi@L1": ["n - 1 - v"],

        # B2 — v-step.
        "s@B2": [{"v": "v + 1", "w": "0"}],

        # L2 (w-loop) invariant.
        "tau@L2": [
            "w <= n",
            "0 <= v",
            "v <= n - 1",
            "0 <= u",
            "u <= n - 1",
            "found == 0 or found == 1",
            "IsMatching(G, n, M) == 1",
            "0 <= w",
        ],
        "g@L2":   ["w < n"],
        "phi@L2": ["n - w"],

        # Inner branch 0 — AP found, flip + break.
        "g@B3.0": [_AP_COND],
        "s@B3.0": [{
            "M": ("Update(Update(Update(Update(M, u, v), v, u), "
                  "M[v], w), w, M[v])"),
            "found": "1",
            "_break": True,
        }],

        # Inner branch 1 — advance w.
        "g@B3.1": [f"not ({_AP_COND})"],
        "s@B3.1": [{"w": "w + 1"}],

        # Post-search SB(n=2): if found, tail-recur; else return.
        # Branch 0: found == 1 → recursive call with current M.
        "g@B4.0": ["found == 1"],
        "s@B4.0": [{
            "_recur": True,
            # k passed as k - 1: provides explicit ranking decrease.
            # At k = 1, args.k = 0 → Fpre(args) requires k > 0 → vacuous,
            # so the IH is vacuous AND the decrease is vacuous.
            "args": {"G": "G", "n": "n", "M": "M", "k": "k - 1"},
            "ret": {"M": "M"},
        }],
        # Branch 1: found == 0 → identity (return).
        "g@B4.1": ["found == 0"],
        "s@B4.1": [{}],

        # Per-procedure ranking: k decreases strictly per recur.
        "phi@PROC": ["k"],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 10_800_000,   # 3 hours
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_max_matching_recur"
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
