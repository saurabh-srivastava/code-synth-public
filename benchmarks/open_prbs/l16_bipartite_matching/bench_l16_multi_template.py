"""bench_l16_multi_template — L1.6 Slice C real benchmark.

Multi-template exploration on a single matching spec.  Wraps three
algorithm shapes for `c-bounded matching on a clique graph`:

  T_A: linear-sweep — `i := 0; while i < n - 1: pair (i, i+1); i += 2`.
       Local i.  Invariant `c >= i`.  Same shape as
       bench_glover_concrete (Slice B.4).

  T_B: two-pointer — `left := 0; right := n - 1;
       while left < right: pair (left, right); left += 1; right -= 1`.
       Locals left, right.  Invariant `c == 2 * left ∧
       left + right == n - 1`.  Distinct algorithm shape.

  T_C: no-op — `SB()` only, no loop.  Initializes c := 0 and exits.
       SHOULD be rejected by the framework: with c == 0, the post
       `c >= n - 1` fails for n > 1.

Common spec:
  Pre  : n >= 0, M = all-(-1), G symmetric, G fully-connected
         (all p ≠ q within [0, n) have G[p][q] >= 1).
  Post : matching-invariant + c >= n - 1.

The clique precondition lets both T_A and T_B validate.  Chain-
graph variants (B.4) work only for T_A; clique is the natural
generalization that admits both pairing strategies.

Each template has its own atoms and its own Tier-3 helper.  The
harness runs all three in parallel subprocesses (RESEARCH.md §I)
and tabulates which templates synthesize.

Observed (2026-05-23, sequential mode, ~969s total):
  T_A (linear-sweep) : PICKED (316s, score 29.50)
  T_B (two-pointer)  : PICKED (652s, score 37.50)
  T_C (no-op)        : rejected (0s — post-bundle fails)
  Best variant      : T_A

The Slice A → Slice C arc:
  Slice A: multi-CANDIDATE at the BODY level via UFs (rejected
           step_skip; picked step_glover + step_greedy_first).
  Slice B: multi-CANDIDATE at the BODY level via concrete ops
           (rejected asymmetric + skip; picked full-pair).
  Slice C: multi-VARIANT at the TEMPLATE level via parallel
           harness (this file).  Picks variants whose templates
           + atoms close all obligations; rejects those that
           can't.
"""
from synth import Problem, SB, Loop, Var
from synth.multi_template import multi_template_solve


_COMMON_PRE = (
    "n >= 0 and "
    "ForAll(lambda k: Implies(0 <= k and k < n, M[k] == -1)) and "
    "ForAll(lambda p, q: Implies("
    "0 <= p and p < n and 0 <= q and q < n, "
    "G[p][q] == G[q][p])) and "
    # Fully-connected (clique): every distinct pair has an edge.
    "ForAll(lambda p, q: Implies("
    "0 <= p and p < n and 0 <= q and q < n and p != q, "
    "G[p][q] >= 1))"
)
_COMMON_POST = (
    "ForAll(lambda k: Implies("
    "0 <= k and k < n and M[k] != -1, "
    "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1)) and "
    "c >= n - 1"
)


T_A_LINEAR_SWEEP = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input")],
    outputs  = [Var("M", "int[]", "output"),
                Var("c", "int",   "output")],
    locals   = [Var("i", "int",   "local")],
    axioms   = ["0 == 0"],
    pre      = _COMMON_PRE,
    post     = _COMMON_POST,

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
        "s@B1":   [{"M": "Update(Update(M, i, i + 1), i + 1, i)",
                    "i": "i + 2",
                    "c": "c + 2"}],
    },
    max_solutions = 1,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_multi_template_A"
    ),
)


T_B_TWO_POINTER = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input")],
    outputs  = [Var("M", "int[]", "output"),
                Var("c", "int",   "output")],
    locals   = [Var("left",  "int", "local"),
                Var("right", "int", "local")],
    axioms   = ["0 == 0"],
    pre      = _COMMON_PRE,
    post     = _COMMON_POST,

    atoms = {
        # left := 0, right := n - 1, c := 0.
        "s@B0": [{"left": "0", "right": "n - 1", "c": "0"}],

        # Two-pointer invariant — relates left + right to n,
        # and c to the number of pairs processed (2 per step).
        # `left <= right + 1` is load-bearing for ranking-lb:
        # phi = right - left + 1, and at loop exit (¬g, i.e.
        # left ≥ right) we have left ≤ right + 1 (advances by
        # 1 per iter from both sides), so phi ≥ 0.
        "tau@L0": [
            "0 <= left",
            "left + right == n - 1",
            ("ForAll(lambda k: Implies("
             "0 <= k and k < n and M[k] != -1, "
             "0 <= M[k] and M[k] < n and G[k][M[k]] >= 1))"),
            "c == 2 * left",
            "left <= right + 1",
        ],
        "g@L0":   ["left < right"],
        "phi@L0": ["right - left + 1"],

        # Pair (left, right) and advance both inward.
        "s@B1":   [{"M": "Update(Update(M, left, right), right, left)",
                    "left": "left + 1",
                    "right": "right - 1",
                    "c": "c + 2"}],
    },
    max_solutions = 1,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_multi_template_B"
    ),
)


T_C_NO_OP = Problem(
    # Trivial template: just initialize, no loop.
    template = SB(),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int",   "input"),
                Var("M", "int[]", "input")],
    outputs  = [Var("M", "int[]", "output"),
                Var("c", "int",   "output")],
    locals   = [],
    axioms   = ["0 == 0"],
    pre      = _COMMON_PRE,
    post     = _COMMON_POST,

    atoms = {
        # No-op: c := 0 and exit.  Post `c >= n - 1` fails for n > 1.
        "s@B0": [{"c": "0"}],
    },
    max_solutions = 1,
    solver_timeout_ms = 600_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_multi_template_C"
    ),
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    # Parallel mode hits Lean type-check contention under load
    # (3 synth subprocesses × N internal Lean workers > CPU
    # capacity → cache lookups time out → spurious unknowns).
    # Use max_workers=1 (sequential dispatch via ProcessPool) for
    # reliable per-variant verification on expensive benchmarks.
    # See RESEARCH.md §I.7 for the parallel-contention analysis.
    result = multi_template_solve(
        variants=[
            ("T_A_linear_sweep", T_A_LINEAR_SWEEP),
            ("T_B_two_pointer",  T_B_TWO_POINTER),
            ("T_C_no_op",        T_C_NO_OP),
        ],
        parallel=True,
        max_workers=1,
    )
    wall = time.monotonic() - t
    print(f"Total wall: {wall:.1f}s")
    print()
    print("=== Slice C exploration table ===")
    print(f"{'#':<3} {'variant':<22} {'status':<14} {'wall':>8} {'score':>8}")
    print("-" * 66)
    for k, v in enumerate(result.variants):
        score = f"{v.score:.2f}" if v.score is not None else "—"
        print(f"{k:<3} {v.name:<22} {v.status:<14} "
              f"{v.elapsed_s:>6.1f}s {score:>8}")
    print()
    if result.best:
        print(f"Best variant: {result.best.name} "
              f"(score {result.best.score:.2f})")
    else:
        print("No variant succeeded.")
    print()
    print("=== Per-variant hints ===")
    for v in result.variants:
        if v.status != "success":
            print(f"-- {v.name} ({v.status}) --")
            reason = getattr(v.result, "reason", None)
            if reason:
                print(f"  reason: {reason}")
            hints = getattr(v.result, "hints", [])
            for h in hints:
                print(f"  hint: {h}")
    print()
    print("Slice A → Slice C arc:")
    print("  Slice A: multi-candidate body via UFs.")
    print("  Slice B: multi-candidate body via concrete ops.")
    print("  Slice C: multi-VARIANT at the TEMPLATE level.")
