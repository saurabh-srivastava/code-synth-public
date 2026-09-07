"""bench_interval_greedy — L1.6 breadth push (1/3): greedy EDF
interval scheduling.

Given n intervals [S[i], E[i]) sorted by end-time, find the
maximum number of pairwise non-overlapping intervals via the
greedy earliest-deadline-first (EDF) algorithm.

  i := 0
  count := 0
  last_end := -1
  while i < n:
      if S[i] >= last_end:
          last_end := E[i]
          count := count + 1
          i := i + 1
      else:
          i := i + 1
  return count

The optimality of greedy EDF is a classical theorem (exchange
argument).  We treat it the same way as Slice 2.C handles
Berge: keep the optimality axiom but verify all other algorithmic
steps concretely.  The UFs `GreedyCount` and `GreedyLastEnd`
encode the recursive definition of what greedy EDF would
produce; the synth then verifies its algorithm matches that.

UFs (2):
  - `GreedyCount(S, E, n)`     : count after processing n intervals.
  - `GreedyLastEnd(S, E, n)`   : last accepted deadline after n iters.

Axioms (3):
  - Base: GreedyCount(S, E, 0) = 0, GreedyLastEnd(S, E, 0) = -1.
  - Accept step: if S[i] >= GreedyLastEnd(S, E, i), then
    GreedyCount(...i+1) = GreedyCount(...i) + 1 and
    GreedyLastEnd(...i+1) = E[i].
  - Skip step: if S[i] < GreedyLastEnd(S, E, i), then
    GreedyCount(...i+1) = GreedyCount(...i) and
    GreedyLastEnd(...i+1) = GreedyLastEnd(...i).

Loop invariant tracks `count = GreedyCount(S, E, i)` and
`last_end = GreedyLastEnd(S, E, i)`.  The synth picks the
correct branch per AP condition; helpers cite the axioms.
"""
from synth import Problem, SB, Loop, Var, solve
from synth.lean_backend.codegen import HelperEntry, HelperRegistry


_MODULE = "SynthLean.Y2Corpus.IntervalGreedy"


# ─── Helper cites ──────────────────────────────────────────────


def _cite_sc_entry_l0(chosen, hyp_for):
    # FLAT shape: L0 entry-bundle after B0 (init).
    return (
        f"exact {_MODULE}.is_sc_entry_l0 "
        "S E n count i last_end "
        "count' i' last_end' "
        "h_pre h_init_i h_init_count h_init_last_end"
    )


def _cite_sc_accept(chosen, hyp_for):
    # Loop body branch 0 (accept).  τ_L0 at body_in + guard + trans.
    # Translator emits trans hyps in order: last_end, count, i.
    return (
        f"exact {_MODULE}.is_sc_accept "
        "S E n count i last_end "
        "count' i' last_end' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 "
        "h_guard h_trans_last_end h_trans_count h_trans_i"
    )


def _cite_sc_skip(chosen, hyp_for):
    # Loop body branch 1 (skip).
    return (
        f"exact {_MODULE}.is_sc_skip "
        "S E n count i last_end "
        "i' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 "
        "h_guard h_trans_i"
    )


def _cite_sc_coverage(chosen, hyp_for):
    # Coverage of the SB(n=2) loop body.  Translator names the loop
    # guard `h_g_loop` (not h_guard).
    return (
        f"exact {_MODULE}.is_sc_coverage "
        "S E n count i last_end "
        "h_pre h_g_loop"
    )


def _cite_sc_final(chosen, hyp_for):
    # L0 final bundle: post-loop, τ + ¬g ⇒ post.
    return (
        f"exact {_MODULE}.is_sc_final "
        "S E n count i last_end count' i' last_end' "
        "h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4 h_not_g"
    )


_TAU_L0_ALL = frozenset({0, 1, 2, 3, 4})


_HELPER_REGISTRY = HelperRegistry(
    module_path="SynthLean.Y2Corpus.interval_greedy.Helpers",
    entries=[
        HelperEntry("is_sc_entry_l0",
            applies_to=lambda k, l, b: k == "safety-bundle-entry" and l == "L0",
            required_atoms={},
            cite=_cite_sc_entry_l0),
        HelperEntry("is_sc_accept",
            applies_to=lambda k, l, b: k == "safety" and l == "L0" and b == 0,
            required_atoms={"tau@L0": _TAU_L0_ALL},
            cite=_cite_sc_accept),
        HelperEntry("is_sc_skip",
            applies_to=lambda k, l, b: k == "safety" and l == "L0" and b == 1,
            required_atoms={"tau@L0": _TAU_L0_ALL},
            cite=_cite_sc_skip),
        HelperEntry("is_sc_coverage",
            applies_to=lambda k, l, b: k == "coverage" and l == "L0",
            required_atoms={},
            cite=_cite_sc_coverage),
        HelperEntry("is_sc_final",
            applies_to=lambda k, l, b: k == "safety-bundle-post" and l == "L0",
            required_atoms={"tau@L0": _TAU_L0_ALL},
            cite=_cite_sc_final),
    ],
)


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("S", "int[]", "input"),    # start times
                Var("E", "int[]", "input"),    # end times
                Var("n", "int", "input")],
    outputs  = [Var("count", "int", "output")],
    locals   = [Var("i", "int", "local"),
                Var("last_end", "int", "local")],

    uninterpreted = [
        ("GreedyCount",   ["int[]", "int[]", "int"], "int"),
        ("GreedyLastEnd", ["int[]", "int[]", "int"], "int"),
    ],

    axioms = [
        # A1 — Base case at n=0.
        "ForAll(lambda S_arr, E_arr: GreedyCount(S_arr, E_arr, 0) == 0)",
        "ForAll(lambda S_arr, E_arr: GreedyLastEnd(S_arr, E_arr, 0) == 0 - 1)",

        # A2 — Accept step: S[i] >= GreedyLastEnd(...,i) ⇒ extends.
        "ForAll(lambda S_arr, E_arr, ii: Implies("
        "   ii >= 0 and S_arr[ii] >= GreedyLastEnd(S_arr, E_arr, ii), "
        "   GreedyCount(S_arr, E_arr, ii + 1) == GreedyCount(S_arr, E_arr, ii) + 1"
        "))",
        "ForAll(lambda S_arr, E_arr, ii: Implies("
        "   ii >= 0 and S_arr[ii] >= GreedyLastEnd(S_arr, E_arr, ii), "
        "   GreedyLastEnd(S_arr, E_arr, ii + 1) == E_arr[ii]"
        "))",

        # A3 — Skip step: S[i] < GreedyLastEnd(...,i) ⇒ preserves.
        "ForAll(lambda S_arr, E_arr, ii: Implies("
        "   ii >= 0 and S_arr[ii] < GreedyLastEnd(S_arr, E_arr, ii), "
        "   GreedyCount(S_arr, E_arr, ii + 1) == GreedyCount(S_arr, E_arr, ii)"
        "))",
        "ForAll(lambda S_arr, E_arr, ii: Implies("
        "   ii >= 0 and S_arr[ii] < GreedyLastEnd(S_arr, E_arr, ii), "
        "   GreedyLastEnd(S_arr, E_arr, ii + 1) == GreedyLastEnd(S_arr, E_arr, ii)"
        "))",
    ],

    pre = (
        "n >= 0 and "
        # Sorted by end-time.
        "ForAll(lambda k1, k2: Implies("
        "  0 <= k1 and k1 < k2 and k2 < n, E[k1] <= E[k2])) and "
        # Each interval is valid: 0 ≤ S[k] < E[k].
        "ForAll(lambda k: Implies("
        "  0 <= k and k < n, 0 <= S[k] and S[k] < E[k]))"
    ),
    post = "count == GreedyCount(S, E, n)",

    atoms = {
        # B0 — init.
        "s@B0": [{"i": "0", "count": "0", "last_end": "0 - 1"}],

        # L0 invariant — 5 atoms.
        "tau@L0": [
            "0 <= i",                                      # 0
            "i <= n",                                      # 1
            "0 <= count",                                  # 2
            "count == GreedyCount(S, E, i)",               # 3
            "last_end == GreedyLastEnd(S, E, i)",          # 4
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Loop body SB(n=2):
        # Branch 0 — accept.
        "g@B1.0": ["S[i] >= last_end"],
        "s@B1.0": [{
            "last_end": "E[i]",
            "count":    "count + 1",
            "i":        "i + 1",
        }],
        # Branch 1 — skip.
        "g@B1.1": ["S[i] < last_end"],
        "s@B1.1": [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,   # 30 min
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/interval_greedy"
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
