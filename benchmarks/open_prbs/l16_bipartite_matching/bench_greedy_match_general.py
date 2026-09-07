"""bench_greedy_match_general — C1.A/B/C: greedy maximal matching on sparse graphs.

The FIRST L1.6 benchmark to:
  - Operate on a SPARSE graph representation (edge list, not int[][]
    adjacency matrix).  Iterates edges directly; no chain/clique
    assumption.
  - Use a MAXIMAL-MATCHING post (not count-bounded).  Asserts no edge
    has both endpoints unmatched at exit — the standard textbook
    maximal-matching certification.

Algorithm — greedy iteration over edges:

  i := 0
  while i < m:
      let u, v = edges[2*i], edges[2*i + 1]
      if M[u] == -1 ∧ M[v] == -1:
          M[u] := v; M[v] := u
      i := i + 1

Spec:
  Pre  : n ≥ 0, m ≥ 0, M all -1, edges well-formed (endpoints in
         [0, n), each edge has distinct endpoints).
  Post : matching-invariant (matched k has 0 ≤ M[k] < n) ∧
         maximal (no edge has both endpoints unmatched).

Design notes recorded in RESEARCH.md §J.  This is the C1
intermediate deliverable — closes C1.A (sparse IR) + C1.B
(maximal post) + C1.C (greedy template).  Does NOT achieve
maximum matching; that's C1.D (multi-week, requires AP).

== Why this is meaningful ==

Slice B and Slice C benchmarks all assumed chain or clique graphs
and used count-bounded posts.  This benchmark drops both:
  - Graph: arbitrary edge list with well-formedness pre.
  - Spec: maximal matching, a textbook correctness criterion.

A solution here demonstrates the framework can synthesize a real
graph algorithm beyond the structured-graph cases.

Observed (2026-05-24, ~864s): 1 solution, score 61.5.  Two
Tier-3 helpers load-bearing — sc2 (full-τ branch-0 inductive,
~80 LOC with `h_extend` lemma) and sc7 (post-bundle, ~10 LOC).
First L1.6 benchmark to operate on an unstructured graph
(arbitrary edge list, no chain/clique restriction).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("edges", "int[]", "input"),
                Var("m",     "int",   "input"),
                Var("n",     "int",   "input"),
                Var("M",     "int[]", "input")],
    outputs  = [Var("M", "int[]", "output")],
    locals   = [Var("i", "int",   "local")],

    # Dummy axiom triggers axiom-heavy Lean routing (same trick as
    # B.1-B.4).  Without it, Z3 returns false-positive SAT verdicts
    # on the quantified-array obligations.
    axioms = ["0 == 0"],

    pre  = (
        "n >= 0 and m >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k < n, M[k] == -1)) and "
        # Edges well-formed: endpoints in range, distinct.
        "ForAll(lambda j: Implies("
        "0 <= j and j < m, "
        "0 <= edges[2*j] and edges[2*j] < n and "
        "0 <= edges[2*j + 1] and edges[2*j + 1] < n and "
        "edges[2*j] != edges[2*j + 1]))"
    ),
    post = (
        # Matching-invariant: matched vertices have valid partner indices.
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        # Maximal: no edge has both endpoints unmatched.
        "ForAll(lambda j: Implies("
        "0 <= j and j < m, "
        "not (M[edges[2*j]] == -1 and M[edges[2*j + 1]] == -1)))"
    ),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= m",
            # Matching-invariant on M at any iteration.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
            # Maximal up to current i: edges 0..i have at least one
            # matched endpoint.
            ("ForAll(lambda j: Implies("
             "0 <= j and j < i, "
             "not (M[edges[2*j]] == -1 and M[edges[2*j + 1]] == -1)))"),
        ],
        "g@L0":   ["i < m"],
        "phi@L0": ["m - i"],

        # Body branches on whether both endpoints are unmatched.
        "g@B1.0": ["M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1"],
        "s@B1.0": [{"M": ("Update(Update(M, edges[2*i], edges[2*i + 1]), "
                          "edges[2*i + 1], edges[2*i])"),
                    "i": "i + 1"}],
        "g@B1.1": ["not (M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1)"],
        "s@B1.1": [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_greedy_match_general"
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
