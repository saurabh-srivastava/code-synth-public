"""bench_glover_explore — L1.6 Slice A: multi-candidate step pool.

The first Slice-A exploration benchmark.  Extends
`bench_glover_verify.py` (single `process_endpoint` UF) with a
POOL of step candidates — the synth framework picks among them.

The pool intentionally includes:
  - 3 candidates with preservation axioms (synth should accept any).
  - 1 candidate with NO preservation axiom (synth should reject).

If the framework picks among the valid candidates while rejecting
the invalid one, Slice A's exploration mechanic is validated:
"the synth framework can pick step functions from a multi-candidate
pool based on which axioms close the obligation chain."

Step candidates:
  - `step_glover(G, M, i)`         — Glover-style sweep step.
  - `step_greedy_first(G, M, i)`   — first-unmatched neighbor.
  - `step_bucket_assign(B, M, i)`  — bucket-based assignment.
  - `step_skip(M, i)`              — no-op (NO axiom; should fail).

Each non-skip step has a `step_<name>_preserves_pm` axiom of the
canonical inductive shape:
  ∀ G n k M, 0 ≤ k < n ∧ is_valid_pm G n k M = 1
    →  is_valid_pm G n (k+1) (step_<name>(...)) = 1

`step_skip` has NO such axiom, so the inductive obligation cannot
close for it — the framework will correctly reject it.

Expected outcome:
  - 3 of 4 candidates produce valid solutions (one per valid step).
  - Synth returns 3+ solutions, each with `s@B1` pointing to a
    different step UF.
  - The skip candidate never appears.

This is the L1.2-pattern speculation at the algorithm-step level.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int", "input"),
                Var("B", "int", "input"),   # bucket structure (opaque)
                Var("n", "int", "input")],
    outputs  = [Var("M", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [
        # Partial-matching predicate.
        ("is_valid_pm", ["int", "int", "int", "int"], "int"),
        # Maximum-matching predicate.
        ("is_max_matching", ["int", "int", "int"], "int"),
        # Initial state.
        ("empty_matching", [], "int"),
        # ---- Candidate step UFs.
        ("step_glover",          ["int", "int", "int"], "int"),
        ("step_greedy_first",    ["int", "int", "int"], "int"),
        ("step_bucket_assign",   ["int", "int", "int"], "int"),
        ("step_skip",            ["int", "int"],        "int"),  # no axiom
    ],

    axioms = [
        # Base: empty matching is valid at k=0.
        "ForAll(lambda G_, n_: is_valid_pm(G_, n_, 0, empty_matching()) == 1)",
        # Termination: valid PM at k=n implies max matching.
        ("ForAll(lambda G_, n_, M_: "
         "Implies(is_valid_pm(G_, n_, n_, M_) == 1, "
         "is_max_matching(G_, n_, M_) == 1))"),
        # Preservation axiom for step_glover (Glover-style sweep).
        ("ForAll(lambda G_, n_, k_, M_: "
         "Implies(0 <= k_ and k_ < n_ and "
         "is_valid_pm(G_, n_, k_, M_) == 1, "
         "is_valid_pm(G_, n_, k_ + 1, step_glover(G_, M_, k_)) == 1))"),
        # Preservation for step_greedy_first.
        ("ForAll(lambda G_, n_, k_, M_: "
         "Implies(0 <= k_ and k_ < n_ and "
         "is_valid_pm(G_, n_, k_, M_) == 1, "
         "is_valid_pm(G_, n_, k_ + 1, "
         "step_greedy_first(G_, M_, k_)) == 1))"),
        # step_bucket_assign deferred to Slice B (requires G ↔ B
        # relationship in the axiom that's awkward without
        # concrete graph IR).
        # step_skip: NO preservation axiom intentionally.
    ],

    pre  = "n >= 0",
    post = "is_max_matching(G, n, M) == 1",
    cost_target = "n",

    atoms = {
        "s@B0": [{"i": "0", "M": "empty_matching()"}],
        "tau@L0": [
            "is_valid_pm(G, n, i, M) == 1",
            "0 <= i",
            "i <= n",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "cost@L0": ["n - i"],
        # ---- POOL of step candidates.
        "s@B1": [
            {"M": "step_glover(G, M, i)", "i": "i + 1"},
            {"M": "step_greedy_first(G, M, i)", "i": "i + 1"},
            # step_bucket_assign deferred — its axiom would need
            # G ↔ B relationship that the current axiom skeleton
            # can't express cleanly.  Re-enable in Slice B with
            # concrete graph IR.
            # {"M": "step_bucket_assign(B, M, i)", "i": "i + 1"},
            {"M": "step_skip(M, i)", "i": "i + 1"},
        ],
    },
    max_solutions = 5,
    expected_solutions = None,    # tabulate what actually happens
    expected_lean_hits = None,
    solver_timeout_ms = 600_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_glover_explore"
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
    # Tabulate which step each solution picks.
    print("=== Slice A exploration table ===")
    print(f"{'#':<3} {'step picked':<25} {'score':>6}")
    print("-" * 50)
    for k, sol in enumerate(result.solutions):
        # Pull the s@B1 atom out of the solution.
        s_b1 = sol.atoms.get("s@B1", {})
        m_rhs = s_b1.get("M", "(unknown)") if isinstance(s_b1, dict) else str(s_b1)
        print(f"{k:<3} {m_rhs:<25} {sol.score:>6.2f}")
    print()
    print("Per-step verdict:")
    for step_name in ["step_glover", "step_greedy_first", "step_skip"]:
        chosen = any(
            isinstance(sol.atoms.get("s@B1"), dict) and
            step_name in sol.atoms["s@B1"].get("M", "")
            for sol in result.solutions
        )
        verdict = "PICKED" if chosen else "rejected"
        print(f"  {step_name:<25} {verdict}")
