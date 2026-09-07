"""bench_max_matching_concrete — C1.D Slice 2.C:
maximum matching via tail-recursive AP search + flip, with
CONCRETE IsMatching predicate + counter-based MatchingSize.

Slice 2.C tightens Slice 2.B's axiomatization:

  - DROPS UFs: MatchingSize, IsMatching.
  - KEEPS UFs: IsMaxMatching, ExistsAugPath.
  - DROPS axioms: size-nonneg, size-bounded, flip-increases-size.
  - REWRITES axioms: Berge + class-restriction now consume the
    CONCRETE IsMatching predicate (3 atoms: range, symmetric,
    edge-in-graph).
  - ADDS local `c : int`, the matching-size counter (incremented
    by 2 per AP-flip in the inner break branch).

The synthesis target stays the same: an algorithm that searches
3-nested for an AP, flips on hit, then tail-recurs.  The proof
substrate is now SIGNIFICANTLY less trusted — only Berge's
theorem + the class-restriction sufficiency claim remain as
axioms.  Everything else (matching invariant, size tracking,
flip preservation) is concrete arithmetic + Lean-proved.

The AP-flip-preserves-IsMatching helper is Tier-1: a real Lean
theorem proven from the AP precondition + the concrete matching
predicate, NOT an axiom.  See Helpers.lean.
"""
from synth import Problem, SB, Loop, Recur, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


_MODULE = "SynthLean.Y2Corpus.L16MaxMatchingConcrete"


# ─── Concrete IsMatching predicate components ─────────────────────
# Four atoms over (G, n, M) capturing "M is a valid matching on G":
#   - range:    M[k] ∈ [0, n)
#   - symmetric: M[M[k]] == k
#   - no_self:  M[k] != k    (matchings exclude self-loops; w/o this
#                              atom the predicate admits the
#                              degenerate "v matched to itself" which
#                              breaks the flip-preserves-IM proof)
#   - edge:     G[k][M[k]] >= 1
# Each conditional on M[k] != -1 (vertex k is matched).
#
# These are SPLIT (β-style) so the framework can pick partial subsets
# and the minimal-required-atoms helper pattern applies (lesson #71).
_MI_RANGE = (
    "ForAll(lambda kk: Implies("
    "0 <= kk and kk < n and M[kk] != -1, "
    "0 <= M[kk] and M[kk] < n))"
)
_MI_SYMM = (
    "ForAll(lambda kk: Implies("
    "0 <= kk and kk < n and M[kk] != -1, "
    "M[M[kk]] == kk))"
)
_MI_NOSELF = (
    "ForAll(lambda kk: Implies("
    "0 <= kk and kk < n and M[kk] != -1, "
    "M[kk] != kk))"
)
_MI_EDGE = (
    "ForAll(lambda kk: Implies("
    "0 <= kk and kk < n and M[kk] != -1, "
    "G[kk][M[kk]] >= 1))"
)

# Same predicate but over (G_mat, m_n, M_arr) bound vars — used in
# axioms where the predicate is universally quantified.
def _mi_inner(G_name: str, n_name: str, M_name: str) -> str:
    """Render the concrete IsMatching predicate as a conjunction of
    the 4 atoms over the given bound-variable names.  Used to inline
    the predicate in axiom bodies.  Uses DIFFERENT bound names per
    atom (kr, ks, kn, ke) to avoid parser confusion when multiple
    `lambda kk` appear at the same lexical level."""
    return (
        f"(ForAll(lambda kr: Implies("
        f"0 <= kr and kr < {n_name} and {M_name}[kr] != -1, "
        f"0 <= {M_name}[kr] and {M_name}[kr] < {n_name})) and "
        f"ForAll(lambda ks: Implies("
        f"0 <= ks and ks < {n_name} and {M_name}[ks] != -1, "
        f"{M_name}[{M_name}[ks]] == ks)) and "
        f"ForAll(lambda kn: Implies("
        f"0 <= kn and kn < {n_name} and {M_name}[kn] != -1, "
        f"{M_name}[kn] != kn)) and "
        f"ForAll(lambda ke: Implies("
        f"0 <= ke and ke < {n_name} and {M_name}[ke] != -1, "
        f"{G_name}[ke][{M_name}[ke]] >= 1)))"
    )


# AP precondition string (shared across guard + the flip helper).
_AP_COND = (
    "v != u and G[u][v] >= 1 and M[v] != -1 and "
    "w != u and w != v and w != M[v] and "
    "M[w] == -1 and G[M[v]][w] >= 1 and M[u] == -1"
)


# ─── Tier-3 helper cites ────────────────────────────────────────
# All helpers updated to use the concrete IsMatching atoms.
# τ atom indices per τ@LX (Slice 2.C layout — to be confirmed once
# the bench drives synth and helpers are authored).
#
# Helper authoring follows the Tier-2-first workflow: axiomatize
# the helper, smoke-test the citation, then promote to Tier-1
# theorem.  See lean/SynthLean/Y2Corpus/l16_max_matching_concrete/
# Helpers.lean for the proof status of each helper.


# τ@L0 layout (8 atoms):
#   0: -1 <= u
#   1: u <= n - 1
#   2: found == 0 or found == 1
#   3: range (concrete IsMatching atom 1)
#   4: symmetric (concrete IsMatching atom 2)
#   5: no_self (concrete IsMatching atom 3)
#   6: edge (concrete IsMatching atom 4)
#   7: c >= 0
_TAU_L0_ATOMS_ALL = frozenset({0, 1, 2, 3, 4, 5, 6, 7})
_TAU_L0_IM_ATOMS = frozenset({3, 4, 5, 6})  # the 4 concrete IsMatching atoms

# τ@L1 layout (10 atoms — same as L0 plus v bounds):
#   0: -1 <= v
#   1: v <= n - 1
#   2: 0 <= u
#   3: u <= n - 1
#   4: found ∈ {0,1}
#   5: range
#   6: symmetric
#   7: no_self
#   8: edge
#   9: c >= 0
_TAU_L1_ATOMS_ALL = frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9})

# τ@L2 layout (12 atoms — same as L1 plus w bounds):
#   0: w <= n
#   1: 0 <= v
#   2: v <= n - 1
#   3: 0 <= u
#   4: u <= n - 1
#   5: found ∈ {0,1}
#   6: range
#   7: symmetric
#   8: no_self
#   9: edge
#  10: 0 <= w
#  11: c >= 0
_TAU_L2_ATOMS_ALL = frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11})


def _cite_sc1(chosen, hyp_for):
    # FLAT shape: bare pre-state + primed for B0-modified.
    return (
        f"exact {_MODULE}.mm_sc1_l0_entry "
        "n k u v w found c M G u' v' w' found' c' "
        "h_pre h_init_found h_init_u h_init_v h_init_w h_init_c"
    )


def _cite_sc2(chosen, hyp_for):
    # τ@L0 enc: 8 atoms (h_enc_tau_0..7).
    return (
        f"exact {_MODULE}.mm_sc2_l1_entry "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 h_enc_tau_6 h_enc_tau_7 h_enc_g "
        "h_i0_trans_u h_i0_trans_v "
        "h_i0_frame_n h_i0_frame_w h_i0_frame_found h_i0_frame_c "
        "h_i0_frame_M h_i0_frame_G"
    )


def _cite_sc3(chosen, hyp_for):
    # τ@L1 enc: 10 atoms (h_enc_tau_0..9).
    return (
        f"exact {_MODULE}.mm_sc3_l2_entry "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 h_enc_tau_6 h_enc_tau_7 "
        "h_enc_tau_8 h_enc_tau_9 h_enc_g "
        "h_i0_trans_v h_i0_trans_w "
        "h_i0_frame_n h_i0_frame_u h_i0_frame_found h_i0_frame_c "
        "h_i0_frame_M h_i0_frame_G"
    )


def _cite_sc5(chosen, hyp_for):
    # τ@L2: 12 atoms (h_tau_0..11).
    return (
        f"exact {_MODULE}.mm_sc5_l2_break "
        "n k u v w found c M G found' c' M' "
        "h_pre "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 "
        "h_tau_6 h_tau_7 h_tau_8 h_tau_9 h_tau_10 h_tau_11 "
        "h_guard h_trans_M h_trans_found h_trans_c"
    )


def _cite_sc6(chosen, hyp_for):
    # τ@L2: 12 atoms.
    return (
        f"exact {_MODULE}.mm_sc6_l2_safety_step "
        "n k u v w found c M G w' "
        "h_pre "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 "
        "h_tau_6 h_tau_7 h_tau_8 h_tau_9 h_tau_10 h_tau_11 "
        "h_guard h_trans_w"
    )


def _cite_sc9(chosen, hyp_for):
    # τ@L1 enc: 10 atoms; τ@L2 i1: 12 atoms.
    return (
        f"exact {_MODULE}.mm_sc9_l1_body_ind "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1 "
        "n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 c_s2 M_s2 G_s2 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 h_enc_tau_6 h_enc_tau_7 "
        "h_enc_tau_8 h_enc_tau_9 h_enc_g "
        "h_i0_trans_v h_i0_trans_w "
        "h_i0_frame_n h_i0_frame_u h_i0_frame_found h_i0_frame_c "
        "h_i0_frame_M h_i0_frame_G "
        "h_i1_L2_tau_0 h_i1_L2_tau_1 h_i1_L2_tau_2 h_i1_L2_tau_3 "
        "h_i1_L2_tau_4 h_i1_L2_tau_5 h_i1_L2_tau_6 h_i1_L2_tau_7 "
        "h_i1_L2_tau_8 h_i1_L2_tau_9 h_i1_L2_tau_10 h_i1_L2_tau_11 "
        "h_i1_L2_frame_n h_i1_L2_frame_u h_i1_L2_frame_v h_i1_L2_frame_G"
    )


def _cite_sc11(chosen, hyp_for):
    # τ@L0 enc: 8 atoms; τ@L1 i1: 10 atoms.
    return (
        f"exact {_MODULE}.mm_sc11_l0_body_ind "
        "n_s0 k_s0 u_s0 v_s0 w_s0 found_s0 c_s0 M_s0 G_s0 "
        "n_s1 k_s1 u_s1 v_s1 w_s1 found_s1 c_s1 M_s1 G_s1 "
        "n_s2 k_s2 u_s2 v_s2 w_s2 found_s2 c_s2 M_s2 G_s2 "
        "h_pre "
        "h_enc_tau_0 h_enc_tau_1 h_enc_tau_2 h_enc_tau_3 "
        "h_enc_tau_4 h_enc_tau_5 h_enc_tau_6 h_enc_tau_7 h_enc_g "
        "h_i0_trans_u h_i0_trans_v "
        "h_i0_frame_n h_i0_frame_w h_i0_frame_found h_i0_frame_c "
        "h_i0_frame_M h_i0_frame_G "
        "h_i1_L1_tau_0 h_i1_L1_tau_1 h_i1_L1_tau_2 h_i1_L1_tau_3 "
        "h_i1_L1_tau_4 h_i1_L1_tau_5 h_i1_L1_tau_6 h_i1_L1_tau_7 "
        "h_i1_L1_tau_8 h_i1_L1_tau_9 h_i1_L1_not_g "
        "h_i1_L1_frame_n h_i1_L1_frame_u h_i1_L1_frame_G"
    )


def _cite_sc14(chosen, hyp_for):
    # τ@L0: 8 atoms (h_tau_0..7).
    return (
        f"exact {_MODULE}.mm_sc14_final_berge "
        "n k u v w found c M G u' v' w' found' c' M' "
        "h_pre "
        "h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 h_tau_6 h_tau_7 h_not_g"
    )


def _cite_sc15(chosen, hyp_for):
    # Coverage of final SB(n=2): need only "found ∈ {0,1}" atom.
    h_found_in_01 = hyp_for("tau@L0", 2)
    return (
        f"exact {_MODULE}.mm_sc15_coverage "
        "n k u v w found c M G "
        f"h_pre {h_found_in_01}"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.l16_max_matching_concrete.Helpers",
    entries=[
        HelperEntry("mm_sc1_l0_entry",
            applies_to=lambda k, l, b: k == "safety-bundle-entry" and l == "L0",
            required_atoms={},  # no τ atoms required (proof uses h_pre only)
            cite=_cite_sc1),
        HelperEntry("mm_sc2_l1_entry",
            applies_to=lambda k, l, b: k == "safety-bundle-entry" and l == "L1",
            required_atoms={"tau@L0": _TAU_L0_ATOMS_ALL},
            cite=_cite_sc2),
        HelperEntry("mm_sc3_l2_entry",
            applies_to=lambda k, l, b: k == "safety-bundle-entry" and l == "L2",
            required_atoms={"tau@L1": _TAU_L1_ATOMS_ALL},
            cite=_cite_sc3),
        HelperEntry("mm_sc5_l2_break",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L2" and b == 0,
            required_atoms={"tau@L2": _TAU_L2_ATOMS_ALL},
            cite=_cite_sc5),
        HelperEntry("mm_sc6_l2_safety_step",
            applies_to=lambda k, l, b: k == "safety" and l == "L2" and b == 1,
            required_atoms={"tau@L2": _TAU_L2_ATOMS_ALL},
            cite=_cite_sc6),
        HelperEntry("mm_sc9_l1_body_ind",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L2" and b is None,
            required_atoms={"tau@L1": _TAU_L1_ATOMS_ALL,
                            "tau@L2": _TAU_L2_ATOMS_ALL},
            cite=_cite_sc9),
        HelperEntry("mm_sc11_l0_body_ind",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L1" and b is None,
            required_atoms={"tau@L0": _TAU_L0_ATOMS_ALL,
                            "tau@L1": _TAU_L1_ATOMS_ALL},
            cite=_cite_sc11),
        HelperEntry("mm_sc14_final_berge",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L0" and b is None,
            required_atoms={"tau@L0": _TAU_L0_ATOMS_ALL},
            cite=_cite_sc14),
        HelperEntry("mm_sc15_coverage",
            applies_to=lambda k, l, b: k == "coverage" and l is None,
            required_atoms={"tau@L0": frozenset({2})},
            cite=_cite_sc15),
    ],
)


# Pre-condition: M is a matching on G, G is symmetric, n >= 0, k > 0.
_PRE = (
    "n >= 0 and "
    "k > 0 and "
    f"{_MI_RANGE} and "
    f"{_MI_SYMM} and "
    f"{_MI_NOSELF} and "
    f"{_MI_EDGE} and "
    "ForAll(lambda p, q: Implies("
    "0 <= p and p < n and 0 <= q and q < n, "
    "G[p][q] == G[q][p]))"
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
                Var("k", "int",   "input")],
    outputs  = [Var("M", "int[]", "output")],
    locals   = [Var("u", "int", "local"),
                Var("v", "int", "local"),
                Var("w", "int", "local"),
                Var("found", "int", "local"),
                Var("c", "int", "local")],   # NEW: matching-size counter

    uninterpreted = [
        ("IsMaxMatching",  ["int[][]", "int", "int[]"], "int"),
        ("ExistsAugPath",  ["int[][]", "int", "int[]"], "int"),
    ],

    axioms = [
        # A1: Berge (concrete) — the 3 IsMatching atoms + ¬ExistsAugPath
        # ⇒ IsMaxMatching.
        "ForAll(lambda G_mat, m_n, M_arr: Implies("
        f"   ({_mi_inner('G_mat', 'm_n', 'M_arr')} and "
        "    ExistsAugPath(G_mat, m_n, M_arr) == 0), "
        "   IsMaxMatching(G_mat, m_n, M_arr) == 1"
        "))",

        # A2: Length-3 search sufficient (class restriction):
        # IsMatching + (no length-3 AP) ⇒ no AP of any length.
        "ForAll(lambda G_mat, m_n, M_arr: Implies("
        f"   ({_mi_inner('G_mat', 'm_n', 'M_arr')} and "
        "    (ForAll(lambda k_u, k_v, k_w: not ("
        "        0 <= k_u and k_u < m_n and "
        "        0 <= k_v and k_v < m_n and "
        "        0 <= k_w and k_w < m_n and "
        "        k_v != k_u and k_w != k_u and k_w != k_v and "
        "        k_w != M_arr[k_v] and M_arr[k_v] != -1 and "
        "        M_arr[k_w] == -1 and M_arr[k_u] == -1 and "
        "        G_mat[k_u][k_v] >= 1 and G_mat[M_arr[k_v]][k_w] >= 1)))), "
        "    ExistsAugPath(G_mat, m_n, M_arr) == 0"
        "))",
    ],

    pre = _PRE,
    post = "IsMaxMatching(G, n, M) == 1",

    atoms = {
        # B0 — init: found=0, u=-1, v=-1, w=0, AND c=0.
        "s@B0": [{"found": "0", "u": "0 - 1", "v": "0 - 1",
                  "w": "0", "c": "0"}],

        # L0 (u-loop) invariant — 8 atoms.
        "tau@L0": [
            "0 - 1 <= u",            # 0
            "u <= n - 1",            # 1
            "found == 0 or found == 1",  # 2
            _MI_RANGE,               # 3
            _MI_SYMM,                # 4
            _MI_NOSELF,              # 5
            _MI_EDGE,                # 6
            "c >= 0",                # 7
        ],
        "g@L0":   ["u + 1 < n and found == 0"],
        "phi@L0": ["n - 1 - u"],

        # B1 — u-step.
        "s@B1": [{"u": "u + 1", "v": "0 - 1"}],

        # L1 (v-loop) invariant — 10 atoms.
        "tau@L1": [
            "0 - 1 <= v",            # 0
            "v <= n - 1",            # 1
            "0 <= u",                # 2
            "u <= n - 1",            # 3
            "found == 0 or found == 1",  # 4
            _MI_RANGE,               # 5
            _MI_SYMM,                # 6
            _MI_NOSELF,              # 7
            _MI_EDGE,                # 8
            "c >= 0",                # 9
        ],
        "g@L1":   ["v + 1 < n and found == 0"],
        "phi@L1": ["n - 1 - v"],

        # B2 — v-step.
        "s@B2": [{"v": "v + 1", "w": "0"}],

        # L2 (w-loop) invariant — 12 atoms.
        "tau@L2": [
            "w <= n",                # 0
            "0 <= v",                # 1
            "v <= n - 1",            # 2
            "0 <= u",                # 3
            "u <= n - 1",            # 4
            "found == 0 or found == 1",  # 5
            _MI_RANGE,               # 6
            _MI_SYMM,                # 7
            _MI_NOSELF,              # 8
            _MI_EDGE,                # 9
            "0 <= w",                # 10
            "c >= 0",                # 11
        ],
        "g@L2":   ["w < n"],
        "phi@L2": ["n - w"],

        # Inner branch 0 — AP found, flip + count++2 + break.
        "g@B3.0": [_AP_COND],
        "s@B3.0": [{
            "M": ("Update(Update(Update(Update(M, u, v), v, u), "
                  "M[v], w), w, M[v])"),
            "found": "1",
            "c": "c + 2",                # NEW: counter increments by 2.
            "_break": True,
        }],

        # Inner branch 1 — advance w.
        "g@B3.1": [f"not ({_AP_COND})"],
        "s@B3.1": [{"w": "w + 1"}],

        # Post-search SB(n=2): if found, tail-recur; else return.
        "g@B4.0": ["found == 1"],
        "s@B4.0": [{
            "_recur": True,
            "args": {"G": "G", "n": "n", "M": "M", "k": "k - 1"},
            "ret": {"M": "M"},
        }],
        "g@B4.1": ["found == 0"],
        "s@B4.1": [{}],

        "phi@PROC": ["k"],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 10_800_000,   # 3 hours
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_max_matching_concrete"
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
