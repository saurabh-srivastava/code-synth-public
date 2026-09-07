"""bench_gale_shapley — L1.6 breadth push (2/3): Gale-Shapley
stable matching via deferred acceptance.

PHASE 2 design — algorithm-level atoms + step axioms.

Algorithm (single outer Loop with mod-cycled proposer):

  init: mate=[-1...], wmate=[-1...], nxt=[0...]
  k_left := k_iter; m := 0
  while k_left > 0:
      w := pref[m][nxt[m]]                    # only meaningful if nxt[m] < n
      # SB(n=3) based on whether m can/should propose:
      if mate[m] != -1 or nxt[m] >= n:
          # SKIP: nothing to do, just cycle.
          pass
      elif wmate[w] == -1 or rank[w][m] < rank[w][wmate[w]]:
          # ACCEPT (free OR displace): w accepts m.
          old := wmate[w]
          mate[old] := -1          # no-op if old == -1
          mate[m] := w
          wmate[w] := m
          nxt[m] := nxt[m] + 1
      else:
          # REJECT: w prefers her current match.
          nxt[m] := nxt[m] + 1
      m := (m + 1) mod n       # all branches advance the proposer cycle
      k_left := k_left - 1

This design avoids the inner scan by cycling m via mod —
correctness preserved (any deterministic schedule of
unprocessed proposers converges to a stable matching, given
sufficient k_iter).

Trust-surface target: Slice 2.C-final-form.
  - 1 classical axiom: GS produces a stable matching at
    convergence.  (NOT in this benchmark's post — left for
    a downstream stability-verification layer.)
  - Recursive UF + step axioms encoding the per-iteration
    GS recursion (analog of interval_greedy's GreedyCount).
  - Concrete invariants in τ for matching well-formedness.
  - Tier-1 Lean theorems for all algorithm-step preservation.

POST: `mate == GSMate(pref, rank, n, k_iter)` — matches the
recursive GS definition, just like interval_greedy's
`count == GreedyCount(S, E, n)`.

The pre asserts mate, wmate, nxt are initialized so the
algorithm doesn't need an init-loop.
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


_MODULE = "SynthLean.Y2Corpus.GaleShapley"


# ─── Step axioms ──────────────────────────────────────────────
# GSMate/GSWMate/GSNxt: arrays-after-iteration-k recursive UFs.
# The step axioms pin per-iteration transitions matching the
# three SB branches: SKIP, ACCEPT, REJECT.
#
# Helper notation: at iteration k, m = m_k (some computed
# proposer; we use mod-cycling so m_k = (something) mod n).
# Because the recursion involves the array values at
# m_k = ((m_init + k) mod n), the axioms parameterize over
# the m_k chosen by the algorithm.

_AXIOMS = [
    # A1 — Base cases at k=0.  GSMate[m] = -1, GSWMate[w] = -1,
    # GSNxt[m] = 0 for all in-range m,w.
    "ForAll(lambda pref_mat, rank_mat, m_n, mm: Implies("
    "  0 <= mm and mm < m_n, "
    "  GSMate(pref_mat, rank_mat, m_n, 0)[mm] == 0 - 1"
    "))",
    "ForAll(lambda pref_mat, rank_mat, m_n, ww: Implies("
    "  0 <= ww and ww < m_n, "
    "  GSWMate(pref_mat, rank_mat, m_n, 0)[ww] == 0 - 1"
    "))",
    "ForAll(lambda pref_mat, rank_mat, m_n, mm: Implies("
    "  0 <= mm and mm < m_n, "
    "  GSNxt(pref_mat, rank_mat, m_n, 0)[mm] == 0"
    "))",
]


# ─── Pre-condition ────────────────────────────────────────────

_PRE = (
    "n >= 1 and "
    "k_iter >= 0 and "
    # Initial state: mate, wmate are all -1; nxt is all 0.
    "ForAll(lambda mm: Implies("
    "  0 <= mm and mm < n, mate[mm] == 0 - 1)) and "
    "ForAll(lambda ww: Implies("
    "  0 <= ww and ww < n, wmate[ww] == 0 - 1)) and "
    "ForAll(lambda mm: Implies("
    "  0 <= mm and mm < n, nxt[mm] == 0)) and "
    # pref / rank well-formed.
    "ForAll(lambda mm, jj: Implies("
    "  0 <= mm and mm < n and 0 <= jj and jj < n, "
    "  0 <= pref[mm][jj] and pref[mm][jj] < n)) and "
    "ForAll(lambda ww, mm: Implies("
    "  0 <= ww and ww < n and 0 <= mm and mm < n, "
    "  0 <= rank[ww][mm] and rank[ww][mm] < n))"
)


# Phase 2 atom design — encodes the actual algorithm.
# τ@L0 carries the recursive-UF equality at each iteration:
# mate, wmate, nxt all match the GS recursion at the current
# `k_iter - k_left` iteration index.
_TAU_L0 = [
    "0 <= k_left",                                     # 0
    "k_left <= k_iter",                                # 1
    "n >= 1",                                          # 2
    # Matching state matches GS recursion at iter k_iter-k_left:
    ("ForAll(lambda mm: Implies("
     "0 <= mm and mm < n, "
     "mate[mm] == GSMate(pref, rank, n, k_iter - k_left)[mm]))"),  # 3
    ("ForAll(lambda ww: Implies("
     "0 <= ww and ww < n, "
     "wmate[ww] == GSWMate(pref, rank, n, k_iter - k_left)[ww]))"),  # 4
    ("ForAll(lambda mm: Implies("
     "0 <= mm and mm < n, "
     "nxt[mm] == GSNxt(pref, rank, n, k_iter - k_left)[mm]))"),  # 5
    "0 <= m_cur",                                      # 6
    "m_cur < n",                                       # 7
]


# Phase 2 step axioms — describe per-iteration GS transitions.
# Each axiom matches one SB(n=3) branch's effect on the GS
# recursion.
#
# To keep this PHASE 2 milestone tractable, we encode the step
# axioms with the proposer-index argument abstract.  The
# algorithm's actual m_cur expression is a mod-cycled counter
# (`m_cur := (m_cur + 1) mod n`); the synth proves at each
# iteration that its chosen mm value matches the GS recursion.
#
# Real GS step axioms span ~10 conjuncts per case (mate, wmate,
# nxt updates × 3 cases).  We capture the structure here but
# many of these will need refinement during the helper-authoring
# phase.

_AXIOMS += [
    # ── SKIP step ──
    # If man mm at iter kk is matched OR out of proposals,
    # state is unchanged.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  (GSMate(pref_mat, rank_mat, m_n, kk)[mm] != 0 - 1 or "
    "   GSNxt(pref_mat, rank_mat, m_n, kk)[mm] >= m_n), "
    "  ForAll(lambda mm2: Implies("
    "    0 <= mm2 and mm2 < m_n, "
    "    GSMate(pref_mat, rank_mat, m_n, kk + 1)[mm2] == GSMate(pref_mat, rank_mat, m_n, kk)[mm2]"
    "  ))"
    "))",
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  (GSMate(pref_mat, rank_mat, m_n, kk)[mm] != 0 - 1 or "
    "   GSNxt(pref_mat, rank_mat, m_n, kk)[mm] >= m_n), "
    "  ForAll(lambda ww: Implies("
    "    0 <= ww and ww < m_n, "
    "    GSWMate(pref_mat, rank_mat, m_n, kk + 1)[ww] == GSWMate(pref_mat, rank_mat, m_n, kk)[ww]"
    "  ))"
    "))",
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  (GSMate(pref_mat, rank_mat, m_n, kk)[mm] != 0 - 1 or "
    "   GSNxt(pref_mat, rank_mat, m_n, kk)[mm] >= m_n), "
    "  ForAll(lambda mm2: Implies("
    "    0 <= mm2 and mm2 < m_n, "
    "    GSNxt(pref_mat, rank_mat, m_n, kk + 1)[mm2] == GSNxt(pref_mat, rank_mat, m_n, kk)[mm2]"
    "  ))"
    "))",

    # ── ACCEPT step ──
    # If man mm at iter kk is free with proposals left, and
    # woman w := pref[mm][nxt[mm]] is free or prefers mm over
    # her current match, then state transitions per ACCEPT.
    # We split into 4 sub-axioms for clarity (mate update for
    # mm, mate update for displaced old_m, wmate update for w,
    # nxt update for mm; non-affected vars unchanged).
    #
    # Use a common precondition variable for readability:
    #   accept_pre := mate[mm]==-1 ∧ nxt[mm]<n ∧
    #                 (wmate[pref[mm][nxt[mm]]]==-1 ∨
    #                  rank[pref[mm][nxt[mm]]][mm] <
    #                  rank[pref[mm][nxt[mm]]][wmate[pref[mm][nxt[mm]]]])
    # The expression is verbose but mechanically straightforward.

    # ACCEPT.A — GSMate[mm] = w (where w = pref[mm][nxt[mm]]).
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "   rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "     rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  GSMate(pref_mat, rank_mat, m_n, kk + 1)[mm] == pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]"
    "))",

    # ACCEPT.B — GSWMate[w] = mm.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "   rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "     rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  GSWMate(pref_mat, rank_mat, m_n, kk + 1)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == mm"
    "))",

    # ACCEPT.C — GSNxt[mm] = old + 1.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "   rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "     rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  GSNxt(pref_mat, rank_mat, m_n, kk + 1)[mm] == GSNxt(pref_mat, rank_mat, m_n, kk)[mm] + 1"
    "))",

    # ── REJECT step ──
    # If man mm at iter kk is free with proposals left, but
    # the woman prefers her current match, only nxt[mm] increments.

    # REJECT.A — GSNxt[mm] = old + 1.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  not (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "       rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "         rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  GSNxt(pref_mat, rank_mat, m_n, kk + 1)[mm] == GSNxt(pref_mat, rank_mat, m_n, kk)[mm] + 1"
    "))",

    # REJECT.B — GSMate unchanged.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  not (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "       rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "         rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  ForAll(lambda mm2: Implies("
    "    0 <= mm2 and mm2 < m_n, "
    "    GSMate(pref_mat, rank_mat, m_n, kk + 1)[mm2] == GSMate(pref_mat, rank_mat, m_n, kk)[mm2]"
    "  ))"
    "))",

    # REJECT.C — GSWMate unchanged.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  not (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "       rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "         rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  ForAll(lambda ww: Implies("
    "    0 <= ww and ww < m_n, "
    "    GSWMate(pref_mat, rank_mat, m_n, kk + 1)[ww] == GSWMate(pref_mat, rank_mat, m_n, kk)[ww]"
    "  ))"
    "))",

    # REJECT.D — GSNxt unchanged for mm2 ≠ mm.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  not (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "       rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "         rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  ForAll(lambda mm2: Implies("
    "    0 <= mm2 and mm2 < m_n and mm2 != mm, "
    "    GSNxt(pref_mat, rank_mat, m_n, kk + 1)[mm2] == GSNxt(pref_mat, rank_mat, m_n, kk)[mm2]"
    "  ))"
    "))",

    # ACCEPT.D — GSMate[mm2] unchanged when mm2 ≠ mm AND mm2 ≠ displaced.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "   rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "     rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  ForAll(lambda mm2: Implies("
    "    0 <= mm2 and mm2 < m_n and mm2 != mm and "
    "    mm2 != GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]], "
    "    GSMate(pref_mat, rank_mat, m_n, kk + 1)[mm2] == GSMate(pref_mat, rank_mat, m_n, kk)[mm2]"
    "  ))"
    "))",

    # ACCEPT.E — GSMate[displaced] = -1 when displacement happens.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] != 0 - 1 and "
    "  rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "    rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]], "
    "  GSMate(pref_mat, rank_mat, m_n, kk + 1)[GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]] == 0 - 1"
    "))",

    # ACCEPT.F — GSWMate[ww] unchanged for ww ≠ w.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "   rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "     rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  ForAll(lambda ww: Implies("
    "    0 <= ww and ww < m_n and ww != pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]], "
    "    GSWMate(pref_mat, rank_mat, m_n, kk + 1)[ww] == GSWMate(pref_mat, rank_mat, m_n, kk)[ww]"
    "  ))"
    "))",

    # ACCEPT.G — GSNxt[mm2] unchanged for mm2 ≠ mm.
    "ForAll(lambda pref_mat, rank_mat, m_n, kk, mm: Implies("
    "  kk >= 0 and 0 <= mm and mm < m_n and "
    "  GSMate(pref_mat, rank_mat, m_n, kk)[mm] == 0 - 1 and "
    "  GSNxt(pref_mat, rank_mat, m_n, kk)[mm] < m_n and "
    "  (GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]] == 0 - 1 or "
    "   rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][mm] < "
    "     rank_mat[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]][GSWMate(pref_mat, rank_mat, m_n, kk)[pref_mat[mm][GSNxt(pref_mat, rank_mat, m_n, kk)[mm]]]]), "
    "  ForAll(lambda mm2: Implies("
    "    0 <= mm2 and mm2 < m_n and mm2 != mm, "
    "    GSNxt(pref_mat, rank_mat, m_n, kk + 1)[mm2] == GSNxt(pref_mat, rank_mat, m_n, kk)[mm2]"
    "  ))"
    "))",
]


_MODULE_LEAN = "SynthLean.Y2Corpus.GaleShapley"


def _cite_sc0(chosen, hyp_for):
    return (
        f"exact {_MODULE_LEAN}.gs_sc0_entry_l0 "
        "n k_iter m_cur k_left mate wmate nxt pref rank "
        "m_cur' k_left' "
        "h_pre h_init_m_cur h_init_k_left"
    )


def _cite_sc1(chosen, hyp_for):
    return (
        f"exact {_MODULE_LEAN}.gs_sc1_coverage "
        "n k_iter m_cur k_left mate wmate nxt pref rank "
        "trivial h_g_loop"
    )


def _cite_sc2(chosen, hyp_for):
    return (
        f"exact {_MODULE_LEAN}.gs_sc2_skip "
        "n k_iter m_cur k_left mate wmate nxt pref rank "
        "m_cur' k_left' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 "
        "h_tau_6 h_tau_7 h_guard h_trans_m_cur h_trans_k_left"
    )


def _cite_sc4(chosen, hyp_for):
    return (
        f"exact {_MODULE_LEAN}.gs_sc4_accept "
        "n k_iter m_cur k_left mate wmate nxt pref rank "
        "m_cur' k_left' mate' wmate' nxt' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 "
        "h_tau_6 h_tau_7 h_guard "
        "h_trans_mate h_trans_wmate h_trans_nxt h_trans_m_cur h_trans_k_left"
    )


def _cite_sc6(chosen, hyp_for):
    return (
        f"exact {_MODULE_LEAN}.gs_sc6_reject "
        "n k_iter m_cur k_left mate wmate nxt pref rank "
        "m_cur' k_left' nxt' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 "
        "h_tau_6 h_tau_7 h_guard "
        "h_trans_nxt h_trans_m_cur h_trans_k_left"
    )


def _cite_sc9(chosen, hyp_for):
    return (
        f"exact {_MODULE_LEAN}.gs_sc9_final "
        "n k_iter m_cur k_left mate wmate nxt pref rank "
        "m_cur' k_left' mate' wmate' nxt' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_tau_5 "
        "h_tau_6 h_tau_7 h_not_g"
    )


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.gale_shapley.Helpers",
    entries=[
        HelperEntry("gs_sc0_entry_l0",
            applies_to=lambda k, l, b: k == "safety-bundle-entry" and l == "L0",
            required_atoms={},
            cite=_cite_sc0),
        HelperEntry("gs_sc1_coverage",
            applies_to=lambda k, l, b: k == "coverage" and l == "L0",
            required_atoms={},
            cite=_cite_sc1),
        HelperEntry("gs_sc2_skip",
            applies_to=lambda k, l, b: k == "safety" and l == "L0" and b == 0,
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6, 7})},
            cite=_cite_sc2),
        HelperEntry("gs_sc4_accept",
            applies_to=lambda k, l, b: k == "safety" and l == "L0" and b == 1,
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6, 7})},
            cite=_cite_sc4),
        HelperEntry("gs_sc6_reject",
            applies_to=lambda k, l, b: k == "safety" and l == "L0" and b == 2,
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6, 7})},
            cite=_cite_sc6),
        HelperEntry("gs_sc9_final",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L0",
            required_atoms={"tau@L0": frozenset({0, 1, 2, 3, 4, 5, 6, 7})},
            cite=_cite_sc9),
    ],
)


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=3)),
    inputs = [Var("pref", "int[][]", "input"),
              Var("rank", "int[][]", "input"),
              Var("n",     "int",   "input"),
              Var("k_iter", "int",  "input")],
    outputs = [Var("mate", "int[]", "output")],
    locals = [Var("wmate", "int[]", "local"),
              Var("nxt",   "int[]", "local"),
              Var("m_cur", "int", "local"),
              Var("k_left", "int", "local")],

    uninterpreted = [
        ("GSMate",   ["int[][]", "int[][]", "int", "int"], "int[]"),
        ("GSWMate",  ["int[][]", "int[][]", "int", "int"], "int[]"),
        ("GSNxt",    ["int[][]", "int[][]", "int", "int"], "int[]"),
    ],

    axioms = _AXIOMS,
    pre = _PRE,
    post = ("ForAll(lambda mm: Implies("
            "0 <= mm and mm < n, "
            "mate[mm] == GSMate(pref, rank, n, k_iter)[mm]))"),

    atoms = {
        # B0 — init: m_cur := 0, k_left := k_iter.
        # mate, wmate, nxt are assumed pre-initialized.
        "s@B0": [{"m_cur": "0", "k_left": "k_iter"}],

        # τ@L0 — recursive-UF equality at current iter.
        "tau@L0": _TAU_L0,
        "g@L0":   ["k_left > 0"],
        "phi@L0": ["k_left"],

        # Loop body SB(n=3):
        # Branch 0 — SKIP: m has nothing to do (matched or out
        # of proposals).
        "g@B1.0": [
            "mate[m_cur] != 0 - 1 or nxt[m_cur] >= n"
        ],
        "s@B1.0": [{
            # SKIP just advances counters.
            "m_cur":  "(m_cur + 1) - ((m_cur + 1) / n) * n",  # (m+1) mod n
            "k_left": "k_left - 1",
        }],

        # Branch 1 — ACCEPT: m proposes to w; w accepts
        # (either free, or prefers m).
        "g@B1.1": [(
            "mate[m_cur] == 0 - 1 and nxt[m_cur] < n and "
            "(wmate[pref[m_cur][nxt[m_cur]]] == 0 - 1 or "
            " rank[pref[m_cur][nxt[m_cur]]][m_cur] < "
            " rank[pref[m_cur][nxt[m_cur]]][wmate[pref[m_cur][nxt[m_cur]]]])"
        )],
        "s@B1.1": [{
            # ACCEPT: update mate, wmate, nxt; advance counters.
            # mate[wmate[w]] := -1 (no-op for free w via out-of-
            # range Update); mate[m_cur] := w; wmate[w] := m_cur.
            "mate":   ("Update(Update(mate, "
                       "wmate[pref[m_cur][nxt[m_cur]]], 0 - 1), "
                       "m_cur, pref[m_cur][nxt[m_cur]])"),
            "wmate":  "Update(wmate, pref[m_cur][nxt[m_cur]], m_cur)",
            "nxt":    "Update(nxt, m_cur, nxt[m_cur] + 1)",
            "m_cur":  "(m_cur + 1) - ((m_cur + 1) / n) * n",
            "k_left": "k_left - 1",
        }],

        # Branch 2 — REJECT: m proposes to w; w rejects.
        "g@B1.2": [(
            "mate[m_cur] == 0 - 1 and nxt[m_cur] < n and "
            "not (wmate[pref[m_cur][nxt[m_cur]]] == 0 - 1 or "
            "     rank[pref[m_cur][nxt[m_cur]]][m_cur] < "
            "     rank[pref[m_cur][nxt[m_cur]]][wmate[pref[m_cur][nxt[m_cur]]]])"
        )],
        "s@B1.2": [{
            "nxt":    "Update(nxt, m_cur, nxt[m_cur] + 1)",
            "m_cur":  "(m_cur + 1) - ((m_cur + 1) / n) * n",
            "k_left": "k_left - 1",
        }],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/gale_shapley"
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
        for h in getattr(result, "hints", [])[:10]:
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for k, sol in enumerate(result.solutions[:1]):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
