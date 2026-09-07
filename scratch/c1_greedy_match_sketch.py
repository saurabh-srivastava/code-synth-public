"""scratch/c1_greedy_match_sketch.py — design validation for C1.A/B/C.

Sketches `bench_greedy_match_general.py`: greedy maximal-matching
on a sparse (edge-list) graph.  Validates that the new spec shape
expands + constraint-generates cleanly without framework changes.

  edges : int[]   length 2m, edges[2i]/edges[2i+1] = i-th edge endpoints.
  m     : int     edge count.
  M     : int[]   matching state (M[k] = partner, -1 if unmatched).
  n     : int     vertex count.

  template = SB() >> Loop(SB(n=2))

  body:
    let u, v = edges[2*i], edges[2*i+1]
    if M[u] == -1 ∧ M[v] == -1:  pair them
    else:                         skip
    i += 1

  post = matching-invariant ∧
         ∀j ∈ [0, m). ¬(M[edges[2j]] == -1 ∧ M[edges[2j+1]] == -1)

Note: this script ONLY does the design validation (expand +
constraints generate cleanly).  Synth would take 30+ min;
running it is C1.C work, not C1.0 design validation.
"""
from synth import Problem, SB, Loop, Var
from synth.expand import expand
from synth.constraints import generate
from collections import Counter


PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("edges", "int[]", "input"),
                Var("m",     "int",   "input"),
                Var("n",     "int",   "input"),
                Var("M",     "int[]", "input")],
    outputs  = [Var("M", "int[]", "output")],
    locals   = [Var("i", "int",   "local")],

    # Dummy axiom triggers axiom-heavy routing (same pattern as
    # B.1-B.4).  Without it, Z3's quantified-array reasoning
    # produces false-positive SAT verdicts.
    axioms = ["0 == 0"],

    pre  = (
        "n >= 0 and m >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k < n, M[k] == -1)) and "
        # Edges are well-formed: endpoints in [0, n).
        "ForAll(lambda j: Implies("
        "0 <= j and j < m, "
        "0 <= edges[2*j] and edges[2*j] < n and "
        "0 <= edges[2*j + 1] and edges[2*j + 1] < n and "
        "edges[2*j] != edges[2*j + 1]))"
    ),
    post = (
        # Matching invariant: matched vertices point to valid partners.
        # (We don't enforce partner symmetry — the maximal post catches
        # that asymmetric pairings leave unmatched edge pairs.)
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        # Maximal: no edge has both endpoints unmatched after the run.
        "ForAll(lambda j: Implies("
        "0 <= j and j < m, "
        "not (M[edges[2*j]] == -1 and M[edges[2*j + 1]] == -1)))"
    ),

    atoms = {
        # SB0: i := 0.
        "s@B0": [{"i": "0"}],

        # Outer τ: tracking progress through edge list.
        # Maximal-invariant inductive: ∀j ∈ [0, i). edge j has
        # at least one matched endpoint after iteration i.
        "tau@L0": [
            "0 <= i",
            "i <= m",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n))"),
            # Per-edge maximal invariant up to current i.
            ("ForAll(lambda j: Implies("
             "0 <= j and j < i, "
             "not (M[edges[2*j]] == -1 and M[edges[2*j + 1]] == -1)))"),
        ],
        "g@L0":   ["i < m"],
        "phi@L0": ["m - i"],

        # Body: SB(n=2).  Branch 0 = both unmatched, pair them.
        # Branch 1 = at least one matched, skip.
        "g@B1.0": ["M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1"],
        "s@B1.0": [{"M": ("Update(Update(M, edges[2*i], edges[2*i + 1]), "
                          "edges[2*i + 1], edges[2*i])"),
                    "i": "i + 1"}],
        "g@B1.1": ["not (M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1)"],
        "s@B1.1": [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = None,
)


def main() -> None:
    """Validate the spec expands + generates cleanly.  No synth."""
    sc = expand(PROBLEM)
    system = generate(PROBLEM, sc)
    print(f"safety constraints: {len(system.safety)}")
    kinds = Counter(c.kind for c in system.safety)
    for k, v in sorted(kinds.items()):
        print(f"  {k}: {v}")
    n_bits = sum(len(b) for b in system.indicators.values())
    n_holes = len(system.indicators)
    print(f"indicators: {n_bits} bits across {n_holes} holes")
    print()
    print("Spec parses + expands + constraints generate cleanly.")
    print("C1.0 design validation: PASS.")
    print()
    print("Next: C1.A doesn't need framework changes (edge list is")
    print("just int[] subscripting).  C1.B's post + τ atom shapes")
    print("are supported.  C1.C is implementation + helper authoring.")


if __name__ == "__main__":
    main()
