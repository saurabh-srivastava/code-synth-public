"""bench_glover_concrete — L1.6 Slice B.4 (L1).

The Slice A → Slice B unification benchmark.  Closes the loop
between:
  - Slice A (bench_glover_explore.py): multi-candidate via UFs;
    `is_valid_pm` / `is_max_matching` / `step_X` all axiomatized.
    Includes `cost_target = "n"` to demonstrate cost-bound dispatch.
  - Slice B.2 (bench_pair_multi_count.py): multi-candidate via
    CONCRETE operations; discrimination via a `c` counter +
    `c >= i` invariant.  No cost target.

B.4 (this file): SAME 3-candidate pool as B.2 (full-pair /
asymmetric / skip) on concrete operations, PLUS `cost_target = "n"`
and `cost@L0 = "n - i"`.  Demonstrates that COST_INVS §1-§4
cost-bound infrastructure (which was built and validated using
UF-axiomatized sub-algorithms in Slice A) composes cleanly with
concrete-operations templates.

Slice A → Slice B unification claim:
  Multi-candidate exploration + cost-bound discrimination works
  WITHOUT UF crutches.  The framework picks Cand 0 (full-pair),
  rejects Cand 1 (asymmetric) and Cand 2 (skip), AND every
  cost obligation closes (linear cost stays in Z3-LIA — no
  NIA tax per CLAUDE.md lesson #56).

Discrimination dimensions:
  - Count:   `c >= i` invariant + `c >= n - 1` post.  Only Cand 0
             preserves the invariant — same mechanism as B.2.
  - Cost:    `cost@L0 = n - i` with `body_cost = 1` per iter
             (SB(n=1) body).  cost-lb: τ ⇒ n - i ≥ 0.
             cost-decrement: 1 ≤ (n-i) - (n-(i+2)) = 2.
             cost-budget: Pre ⇒ n - 0 ≤ n.  All linear; Z3-LIA
             closes them on the picked Cand 0 cube.  Cost
             obligations pass for the candidates THAT pass the
             other checks — cost is a unifying validation, not
             an extra discrimination axis.

Observed (2026-05-23, ~441s):
  - Cand 0 (full-pair):   PICKED   (1 solution, score 30.50).
  - Cand 1 (asymmetric):  rejected (c >= i unpreserved).
  - Cand 2 (skip):        rejected (c >= i unpreserved).

Tier-3 helper: ports B.2's sc1_fallthrough_f16e259e to the new
cost-augmented signature (extra h_cost_target binding).  ~60 LOC.

Slice B totals after this benchmark closes:
  - B.1: bench_pair_consecutive E2E (1 sol, 695s).
  - B.2: bench_pair_multi_count concrete discrimination (1 sol,
         405s, 3-candidate pool).
  - B.3: emit_py + emit_c + emit_rust round-trip + int[][]
         emitter extensions.
  - B.4: bench_glover_concrete — cost-bound on concrete ops.
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

    # Trivial axiom triggers axiom-heavy Lean routing (B.1/B.2
    # pattern — required for the quantified-array obligations).
    axioms = ["0 == 0"],

    pre  = (
        "n >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k < n, M[k] == -1)) and "
        "ForAll(lambda p, q: Implies("
        "0 <= p and p < n and 0 <= q and q < n, "
        "G[p][q] == G[q][p])) and "
        # Chain graph — count post `c >= n - 1` is achievable.
        "ForAll(lambda k: Implies(0 <= k and k < n - 1, "
        "G[k][k + 1] >= 1))"
    ),
    post = (
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1)) and "
        "c >= n - 1"
    ),

    # Cost-bound: linear cost target.  Tests COST_INVS §1-§4
    # infrastructure on concrete operations.
    cost_target = "n",

    atoms = {
        "s@B0": [{"i": "0", "c": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1))"),
            "c >= i",
        ],
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - i"],
        # Cost atom — Slice A used the same expression.
        "cost@L0": ["n - i"],

        # Multi-candidate pool (same as B.2).
        "s@B1": [
            # Cand 0: full pair.
            {"M": "Update(Update(M, i, i + 1), i + 1, i)",
             "i": "i + 2",
             "c": "c + 2"},
            # Cand 1: asymmetric.
            {"M": "Update(M, i, i + 1)",
             "i": "i + 2",
             "c": "c + 1"},
            # Cand 2: skip.
            {"i": "i + 2",
             "c": "c"},
        ],
    },
    max_solutions = 3,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_glover_concrete"
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

    print("=== Slice B.4 (L1) exploration table ===")
    print(f"{'#':<3} {'pairing strategy':<55} {'score':>6}")
    print("-" * 70)
    cand_labels = {
        "Update(Update(M, i, i + 1), i + 1, i)": "Cand 0: full-pair  (M[i]=i+1, M[i+1]=i)",
        "Update(M, i, i + 1)":                  "Cand 1: asymmetric (M[i]=i+1 only)",
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
    print()
    print("Slice A → Slice B unification: cost-bound infrastructure")
    print("composes with concrete operations.  No UFs.")
