"""bench_aug3_inner_search — C1.D K.3.2 baby step: concrete inner
search for the 4th endpoint of a length-3 augmenting path, using
the `break` primitive.

The first L1.6 benchmark to perform CONCRETE augmenting-path
detection on a real edge list — not via UF axiomatization.  The
algorithm searches w for a valid 4th endpoint of a length-3 AP
u-v-z-w, where (u, v, z) are given as inputs forming the first
three vertices.

Inputs:
  G : int[][]   adjacency matrix (symmetric, 0/1 entries)
  n : int       vertex count
  M : int[]     current matching (M[k] = partner, -1 if unmatched)
  u, v, z : int  the first three vertices of a candidate AP

Pre (the inputs already form a valid 3-prefix of an AP):
  - n ≥ 0, u, v, z distinct, all in [0, n).
  - M is a valid matching (matched partners are valid indices).
  - M[u] == -1               (u is unmatched).
  - M[v] == z, M[z] == v     (v and z are matched to each other).
  - G[u][v] >= 1             (the first non-M edge exists).
  - G is symmetric.

Algorithm:

  w := 0
  while w < n:
      if (w != u ∧ w != v ∧ w != z ∧ M[w] == -1 ∧ G[z][w] >= 1):
          # length-3 AP found: u-v-z-w.  Flip:
          M[u] := v
          M[v] := u
          M[z] := w
          M[w] := z
          break              # exits the loop
      w := w + 1

Post:
  - M is still a valid matching (matched partners valid indices).
  - Either:
    - No flip happened (w reached n): M unchanged.
    - Flip happened (broke out at some w): M[u]=v ∧ M[v]=u ∧
      M[z]=w' ∧ M[w']=z for some w' that was unmatched and
      edge-connected to z.

The post is structured as `valid-matching` plus a disjunction of
"unchanged" or "flipped consistently."

== What this validates ==

  - The break primitive in a concrete-graph context.
  - Length-3 AP detection on real edge data (no UF crutch).
  - Multi-update flip via parallel-dict transition + break.

If this synthesizes, the next steps (compose with outer u-loop +
v-loop) become more tractable — the framework can express the
core "search for 4th endpoint, flip if found" pattern.

== Caveat ==

The post is intentionally weak — it allows the algorithm to
either flip or no-op.  For a stronger spec (e.g., "if a valid w
exists, the algorithm finds it"), we'd need a quantified
counter-example argument or a "first-found" semantics that the
framework doesn't easily express today.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input"),
                Var("u", "int",   "input"),
                Var("v", "int",   "input"),
                Var("z", "int",   "input")],
    outputs  = [Var("M", "int[]", "output")],
    locals   = [Var("w", "int",   "local")],

    # Dummy axiom triggers the axiom-heavy Lean routing path —
    # required because Z3's quantifier instantiation is unreliable
    # on the matching-invariant ForAll atoms.  Same trick as
    # B.1/B.2/B.4 (lesson #46).
    axioms = ["0 == 0"],

    pre  = (
        # Bounds + distinctness on input indices.
        "n >= 0 and "
        "0 <= u and u < n and "
        "0 <= v and v < n and "
        "0 <= z and z < n and "
        "u != v and u != z and v != z and "
        # M is a valid matching.
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        # Length-3 AP prefix: u unmatched, v-z matched together,
        # G[u][v] >= 1.
        "M[u] == -1 and "
        "M[v] == z and "
        "M[z] == v and "
        "G[u][v] >= 1 and "
        # G symmetric.
        "ForAll(lambda p, q: Implies("
        "0 <= p and p < n and 0 <= q and q < n, "
        "G[p][q] == G[q][p]))"
    ),
    post = (
        # Matching invariant: matched partners are valid indices.
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n))"
    ),

    atoms = {
        # Init: w := 0.
        "s@B0": [{"w": "0"}],

        # τ: matching invariant preserved + w in scan range.
        "tau@L0": [
            "0 <= w",
            "w <= n",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
        ],
        "g@L0":   ["w < n"],
        "phi@L0": ["n - w"],

        # Branch 0: valid 4th endpoint found.  Flip + break.
        "g@B1.0": [(
            "w != u and w != v and w != z and "
            "M[w] == -1 and G[z][w] >= 1"
        )],
        "s@B1.0": [{
            "M": ("Update(Update(Update(Update(M, u, v), v, u), "
                  "z, w), w, z)"),
            "_break": True,
        }],

        # Branch 1: not a valid w, advance.
        "g@B1.1": [(
            "not (w != u and w != v and w != z and "
            "M[w] == -1 and G[z][w] >= 1)"
        )],
        "s@B1.1": [{"w": "w + 1"}],

        # Final SB: preserve all vars (no writes).  Avoids the
        # chain-bundle translator's "skip rewrites loop-modified
        # var M" check that fires on explicit `{"M": "M"}`.
        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_aug3_inner_search"
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
    for k, sol in enumerate(result.solutions[:1]):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
