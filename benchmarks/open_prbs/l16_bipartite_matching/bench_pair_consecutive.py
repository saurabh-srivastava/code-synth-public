"""bench_pair_consecutive — L1.6 Slice B (first concrete benchmark).

The first L1.6 benchmark with CONCRETE matching operations (not
UFs).  Algorithm: "pair consecutive vertices (i, i+1) if an edge
exists between them."  Simple matching (not maximal, not maximum)
— but uses REAL operations on `int[]` (matching) and `int[][]`
(adjacency).

  for i := 0, 2, 4, ...; i < n - 1:
      if G[i][i + 1] >= 1:
          M[i]     := i + 1
          M[i + 1] := i
      i := i + 2

== Slice B.1 OUTCOME (2026-05-23) ==

E2E SYNTHESIS in 695s with 1 verified solution.  First L1.6
benchmark with CONCRETE matching operations (not UFs):
  - int[][] adjacency matrix reads (`G[i][i+1]`).
  - int[] matching with nested Update (`Update(Update(M, i, i+1),
    i+1, i)`).
  - Branched body (SB(n=2)) on edge existence.
  - Quantified pre/post over the matching contents.

The synth selected the minimal τ = {0 ≤ i, i ≤ n,
matching-invariant} — the unmatched-tail atom was redundant
under conjunctive enumeration (Phase 3.L's monotonicity logic
applied at the Boolean level even with axiom-heavy routing
disabling the fast-path).

The load-bearing Tier-3 helper is
`sc2_fallthrough_cb44bbf0.solved.lean`: case-split on
k = i, k = i+1, otherwise, applying G symmetry via h_pre_sym
for the k=i+1 case.  ~50 LOC.  Closes the inductive
preservation of matching-invariant under branch-0 (edge
exists, pair (i, i+1)).
"""

from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n",  "int",   "input"),
                Var("M",  "int[]", "input")],
    outputs  = [Var("M",  "int[]", "output")],
    locals   = [Var("i",  "int",   "local")],

    # Trivial axiom to trigger the framework's axiom-heavy routing,
    # which Lean-cross-checks Z3 SAT verdicts on safety-bundle-post.
    # Without this, Z3's false-positive SAT on quantified-array
    # obligations silently rejects the load-bearing τ subset.
    # Lesson banked: quantified-array obligations need Lean
    # cross-check even without UF axioms in scope.
    axioms = ["0 == 0"],

    pre  = (
        "n >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k < n, M[k] == -1)) and "
        # G is symmetric so M[i+1]=i and M[i]=i+1 both have edges.
        "ForAll(lambda p, q: Implies("
        "0 <= p and p < n and 0 <= q and q < n, "
        "G[p][q] == G[q][p]))"
    ),
    # B.1.2 POST: matched partners are valid indices AND the edge
    # exists (G[k][M[k]] >= 1).  Adds the edge-check on top of the
    # B.1 baseline.  M[M[k]]=k symmetry deferred to B.1.3.
    post = (
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1))"
    ),

    atoms = {
        # SB0: i := 0.
        "s@B0": [{"i": "0"}],

        # Outer τ — essentials only.  n ≥ 0 dropped (h_pre carries
        # it).  i ≤ n is load-bearing for ranking-lb (phi = n - i).
        # Axiom-heavy routing disables Phase 3.L monotonicity
        # fast-path, so every τ atom costs a 2× enumeration factor.
        "tau@L0": [
            "0 <= i",
            "i <= n",
            # Matched partners are valid indices and edges exist.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1))"),
            # Vertices ≥ i are unmatched (-1) — pre carried forward.
            ("ForAll(lambda k: Implies("
             "i <= k and k < n, M[k] == -1))"),
        ],
        # Loop while at least one pair remains.
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - i"],

        # Body: SB(n=2) — branch on edge existence.
        # Use ≥ 1 / ≤ 0 (complete over Int) instead of == 1 / == 0
        # so coverage `G[i][i+1] ≥ 1 ∨ G[i][i+1] ≤ 0` is trivially
        # provable by omega.
        # Branch 0: edge exists, pair them.
        "g@B1.0": ["G[i][i + 1] >= 1"],
        "s@B1.0": [{"M": "Update(Update(M, i, i + 1), i + 1, i)",
                    "i": "i + 2"}],
        # Branch 1: no edge, skip.
        "g@B1.1": ["G[i][i + 1] <= 0"],
        "s@B1.1": [{"i": "i + 2"}],
    },
    max_solutions = 3,
    expected_solutions = None,   # B.1: simplified post; testing if this closes.
    expected_lean_hits = None,
    solver_timeout_ms = 600_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_pair_consecutive"
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
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n_idx, sol in enumerate(result.solutions[:3]):
        print(f"── solution #{n_idx} (score={sol.score:g}) ──")
        print(sol.code)
        print()
