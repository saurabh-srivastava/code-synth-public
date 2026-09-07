"""bench_glover_verify — L1.6 (1) end-to-end synthesis (SAT).

The first cost-bound matching benchmark to synthesize end-to-end.
Validates that the synth framework can EXPRESS graph-flavored
matching problems via UF + inline axioms AND close both
correctness AND cost obligations via Lean dispatch.

Problem shape:
  Inputs:  G (adjacency UF), n (vertex count).
  Output:  M (matching, UF-valued).
  Pre:     n ≥ 0.
  Post:    is_max_matching(G, n, M) == 1.
  Cost:    target = n  (linear in vertex count).

Template:
  i := 0;  M := empty_matching();
  while (i < n):
      M := process_endpoint(M, i);    // abstract step (UF)
      i := i + 1;
  // post: is_max_matching(G, n, M) == 1

Per-iteration semantics axiomatized:
  - user_axiom_0: empty_matching is a valid PM at k=0.
  - user_axiom_1: process_endpoint preserves validity.
  - user_axiom_2: valid PM at k=n implies max matching.

== Tier-3 helper needed (and provided) ==

The synth framework's generic Lean tactic chain (`aesop`,
`simp_all`) doesn't instantiate the universally-quantified
user_axiom_2 cleanly when the post-bundle obligation needs
"is_max_matching G n M' = 1" derived from
"is_valid_pm G n i' M' = 1 ∧ i' = n (via guard exit)".

Companion file:
  lean/SynthLean/Y2Corpus/l16_glover_verify/
      sc7_fallthrough_62a3480b.solved.lean

provides an explicit proof:
    have hi : i' = n := by omega
    rw [hi] at h_tau_0
    exact user_axiom_2 G n M' h_tau_0

With this one .solved.lean alongside the framework's auto-
dumped .failed.lean files, the benchmark closes:

  wall: ~3 minutes (Lean dispatch dominated).
  Result: 1 solution, with τ = {is_valid_pm, 0≤i, i≤n},
          φ = n-i, cost@L = n-i, against cost_target = "n".

This is the L1.6 (1) end-to-end synthesis deliverable.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int", "input"),   # adjacency-graph handle (opaque)
                Var("n", "int", "input")],
    outputs  = [Var("M", "int", "output")], # matching handle (opaque)
    locals   = [Var("i", "int", "local")],

    uninterpreted = [
        # Partial-matching predicate: is_valid_pm(G, n, k, M) means
        # M is a valid matching on G restricted to processing
        # endpoints [0, k).
        ("is_valid_pm", ["int", "int", "int", "int"], "int"),
        # is_max_matching(G, n, M) means M is a maximum matching.
        ("is_max_matching", ["int", "int", "int"], "int"),
        # empty_matching: the empty matching as a constant.
        ("empty_matching", [], "int"),
        # process_endpoint(M, i): apply Glover's step at endpoint i.
        ("process_endpoint", ["int", "int"], "int"),
    ],

    axioms = [
        # Base: empty matching is valid at k=0.
        "ForAll(lambda G_, n_: is_valid_pm(G_, n_, 0, empty_matching()) == 1)",
        # Inductive step: process_endpoint preserves validity.
        ("ForAll(lambda G_, n_, k_, M_: "
         "Implies(0 <= k_ and k_ < n_ and "
         "is_valid_pm(G_, n_, k_, M_) == 1, "
         "is_valid_pm(G_, n_, k_ + 1, process_endpoint(M_, k_)) == 1))"),
        # Termination: at k = n, the partial matching IS a max matching.
        ("ForAll(lambda G_, n_, M_: "
         "Implies(is_valid_pm(G_, n_, n_, M_) == 1, "
         "is_max_matching(G_, n_, M_) == 1))"),
    ],

    pre  = "n >= 0",
    post = "is_max_matching(G, n, M) == 1",
    cost_target = "n",

    atoms = {
        # SB0: initialize i, M.
        "s@B0": [{"i": "0", "M": "empty_matching()"}],
        # Loop invariant: valid partial matching up to current i.
        "tau@L0": [
            "is_valid_pm(G, n, i, M) == 1",     # the load-bearing one
            "0 <= i",
            "i <= n",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "cost@L0": [
            "n - i",      # ← published: cost per remaining iteration = 1
            "n",          # fails (B): no decrement
        ],
        # Body: M := process_endpoint(M, i); i := i + 1.
        "s@B1": [{"M": "process_endpoint(M, i)", "i": "i + 1"}],
    },
    max_solutions = 3,
    expected_solutions = 1,
    expected_lean_hits = None,   # Many; varies per machine load.
    solver_timeout_ms = 300_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_glover_verify"
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
    for k, sol in enumerate(result.solutions[:3]):
        print(f"── solution #{k} (score={sol.score:g}) ──")
        print(sol.code)
        print()
