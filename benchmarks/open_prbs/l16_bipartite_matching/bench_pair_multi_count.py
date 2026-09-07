"""bench_pair_multi_count — L1.6 Slice B.2 (multi-candidate at the
concrete level).

Extends bench_pair_consecutive (Slice B.1) with a POOL of candidate
body transitions and a COUNT-BOUNDED post that discriminates them.

The 'count' is a real program variable `c: int` rather than a UF.
Each candidate proposes its own (M-update, i-update, c-update)
triple:

  - Cand 0 (full-pair):  M[i]:=i+1, M[i+1]:=i, i+=2, c+=2.
  - Cand 1 (asymmetric): M[i]:=i+1 only,         i+=2, c+=1.
  - Cand 2 (skip):       no M update,            i+=2, c+=0.

The invariant `c >= i` is preserved ONLY by Cand 0 (each iteration
increments i by 2; the count must keep pace).  Cand 1 falls behind
by 1 per step; Cand 2 falls behind by 2.  At loop exit, ¬g gives
`i >= n - 1`, so `c >= i >= n - 1` discharges the post.

Observed (2026-05-23, ~405s):
  - Cand 0 (full-pair):  PICKED   (1 solution, score 29.5).
  - Cand 1 (asymmetric): rejected (can't preserve c >= i).
  - Cand 2 (skip):       rejected (can't preserve c >= i).

This is the concrete-operations analog of Slice A's
bench_glover_explore: the framework picks among CONCRETE
candidates based on which inductive obligations close, not on
which UF axioms exist.  No UFs in this benchmark.

== Helpers needed ==

Cand 0 needs a Tier-3 sc2 helper similar to
sc2_fallthrough_cb44bbf0.solved.lean from B.1, but with `c >= i`
added as a tracked atom.  Distinct signature hash because the
state binders now include `c`/`c'`.

Cand 1 and Cand 2 should NOT need helpers — their sc2
obligations are GENUINELY INVALID (no τ subset including c >= i
preserves it).  The framework will dump their .failed.lean files
and correctly reject them.

== Spec discrimination rationale ==

A chain-graph pre (`G[k][k+1] >= 1 for all k`) is the simplest
class where:
  - Cand 0 achieves c = 2 * floor((n-1)/2 + 1) ≥ n - 1 (post passes).
  - Cand 1 achieves c = floor((n-1)/2 + 1) < n - 1 for n ≥ 3 (fails).
  - Cand 2 achieves c = 0 (fails for any n ≥ 2).

For benchmarks beyond chain graphs (real bipartite matching), the
post would need to be augmented with augmenting-path-free
arguments or per-graph-class lower bounds.  That's Slice B.4 /
Slice C territory.

== Runtime expectations ==

3 candidates × ~16 τ subsets × ~5 constraints × ~5s Lean dispatch
= 20-40 minutes wall-clock.  May be longer if Lean's tactic chain
hits timeouts on the τ-with-c subsets.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input")],
    outputs  = [Var("M", "int[]", "output"),
                Var("c", "int",   "output")],
    locals   = [Var("i", "int",   "local")],

    # Trivial axiom triggers axiom-heavy Lean routing — same trick
    # as B.1.  Without it, Z3 returns false-positive SAT on the
    # quantified-array safety obligations.
    axioms = ["0 == 0"],

    pre  = (
        "n >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k < n, M[k] == -1)) and "
        "ForAll(lambda p, q: Implies("
        "0 <= p and p < n and 0 <= q and q < n, "
        "G[p][q] == G[q][p])) and "
        # Chain graph: edges between consecutive vertices.  Makes
        # the count post `c >= n - 1` achievable (Cand 0 is the only
        # candidate that reaches it).
        "ForAll(lambda k: Implies(0 <= k and k < n - 1, "
        "G[k][k + 1] >= 1))"
    ),
    post = (
        # Matching-invariant: matched partners are valid + edges exist.
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1)) and "
        # Count post: discriminates candidates.  Only achievable
        # when the body picks Cand 0 every iteration.
        "c >= n - 1"
    ),

    atoms = {
        # SB0: i := 0; c := 0.
        "s@B0": [{"i": "0", "c": "0"}],

        # Outer τ: 4 atoms.  `c >= i` is the load-bearing one for
        # discrimination — Cand 1 and Cand 2 can't preserve it.
        "tau@L0": [
            "0 <= i",
            "i <= n",
            # Matching invariant (concrete, no UFs).
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1))"),
            # Count invariant — load-bearing for the count post.
            "c >= i",
        ],
        # Loop while at least one pair remains.
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - i"],

        # ── POOL of body candidates ──
        # Single-branch body (no SB(n=2)); the multi-candidate work
        # happens at the s@B1 level.  Synth picks among Cand 0/1/2.
        "s@B1": [
            # Cand 0: full pair (i, i+1).  c += 2.
            {"M": "Update(Update(M, i, i + 1), i + 1, i)",
             "i": "i + 2",
             "c": "c + 2"},
            # Cand 1: asymmetric — only mark M[i].  c += 1.
            {"M": "Update(M, i, i + 1)",
             "i": "i + 2",
             "c": "c + 1"},
            # Cand 2: skip.  c unchanged.
            {"i": "i + 2",
             "c": "c"},
        ],
    },
    max_solutions = 3,
    expected_solutions = None,    # tabulate what actually picks
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,    # 30 min — multi-candidate has 3× the obligation count
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_pair_multi_count"
    ),
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
    print(f"Found {len(result.solutions)} solution(s).")
    print()

    # Tabulate which candidate each solution picked.
    print("=== Slice B.2 exploration table ===")
    print(f"{'#':<3} {'pairing strategy':<55} {'score':>6}")
    print("-" * 70)
    cand_labels = {
        "Update(Update(M, i, i + 1), i + 1, i)": "Cand 0: full-pair  (M[i]=i+1, M[i+1]=i)",
        "Update(M, i, i + 1)":                  "Cand 1: asymmetric (M[i]=i+1 only)",
        # Skip has no M update — recognized by absence of "M" key.
    }
    picked = set()
    for k, sol in enumerate(result.solutions):
        s_b1 = sol.atoms.get("s@B1", {})
        m_rhs = s_b1.get("M") if isinstance(s_b1, dict) else None
        if m_rhs is None:
            label = "Cand 2: skip       (no M update)"
        else:
            label = cand_labels.get(m_rhs, f"unknown: {m_rhs}")
        picked.add(label)
        print(f"{k:<3} {label:<55} {sol.score:>6.2f}")
    print()
    print("Per-candidate verdict:")
    for label in ("Cand 0: full-pair  (M[i]=i+1, M[i+1]=i)",
                  "Cand 1: asymmetric (M[i]=i+1 only)",
                  "Cand 2: skip       (no M update)"):
        verdict = "PICKED" if label in picked else "rejected"
        print(f"  {label:<55} {verdict}")
