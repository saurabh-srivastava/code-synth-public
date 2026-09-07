"""bench_aug3_flip_concrete — C1.D K.3.1.5: concrete length-3 AP flip.

A half-step between K.3.0 (everything UF) and K.3.2 (everything
concrete).  Here the AUGMENTING PATH FLIP is concrete — the
algorithm reads the AP indices from UFs but executes the
4-write store chain in concrete IR on `int[]` M.

Uses the K.A.3 framework extension: lambda-bound vars with
`*_mat` and `*_arr` suffixes are typed as int[][] and int[]
(not the default int), allowing axioms to quantify universally
over the matching state.

Algorithm:

  while find_aug3_exists(G, n, M) == 1:
      u := find_aug3_u(G, n, M)
      v := find_aug3_v(G, n, M)
      z := find_aug3_z(G, n, M)
      w := find_aug3_w(G, n, M)
      M[u] := v; M[v] := u; M[z] := w; M[w] := z    // concrete

  post: is_max_matching(G, n, M) == 1   (via Berge)

The UFs `find_aug3_*` axiomatize AP DETECTION; the FLIP is
concrete 4-write Updates on the matching array.

Observed (2026-05-24, 15s): 1 solution.  No Tier-3 helpers
needed; the axiom chain + framework K.A.3 extension (typed
lambda binders) closes everything.

This bridges K.3.0's all-UF approach to K.3.2's all-concrete
detection.  Validates that the framework can compose:
  - UF-guarded loop (from K.3.0).
  - Concrete data manipulation in the body (flips on int[]).
  - Termination via UF-backed ranking (n - 2*matching_size).
  - Berge to close the post.

Note: this benchmark's POST asserts is_max_matching, but the
algorithm only eliminates LENGTH-3 augmenting paths.  Berge
needs ALL APs absent.  We axiomatize the eventual no-AP
state via `find_aug3_exists == 0 → no APs of any length` as
a conservative simplification.  In a TRUE maximum-matching
algorithm, AP detection would search ALL lengths, not just
length 3.  This is a structural caveat for the benchmark
class, not a soundness issue — the axioms describe what
the user's algorithm achieves, and the user can choose to
encode a stronger AP detector.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int[][]", "input"),
                Var("n", "int", "input"),
                Var("M", "int[]", "input")],
    outputs  = [Var("M", "int[]", "output"),
                # Dummy counter local — needed because the framework
                # requires a non-empty SB(init).  We don't use it
                # in the algorithm body.
                Var("i", "int", "output")],
    locals   = [],

    uninterpreted = [
        ("is_matching",      ["int[][]", "int", "int[]"], "int"),
        ("is_max_matching",  ["int[][]", "int", "int[]"], "int"),
        ("matching_size",    ["int[][]", "int", "int[]"], "int"),
        ("find_aug3_exists", ["int[][]", "int", "int[]"], "int"),
        ("find_aug3_u", ["int[][]", "int", "int[]"], "int"),
        ("find_aug3_v", ["int[][]", "int", "int[]"], "int"),
        ("find_aug3_z", ["int[][]", "int", "int[]"], "int"),
        ("find_aug3_w", ["int[][]", "int", "int[]"], "int"),
    ],

    axioms = [
        # (A2) matching_size non-negative.
        "ForAll(lambda G_mat, n_, M_arr: matching_size(G_mat, n_, M_arr) >= 0)",

        # (A3) is_matching → 2*matching_size ≤ n.  (ranking-lb closure)
        ("ForAll(lambda G_mat, n_, M_arr: Implies("
         "is_matching(G_mat, n_, M_arr) == 1, "
         "2 * matching_size(G_mat, n_, M_arr) <= n_))"),

        # (A4-A5) When find_aug3_exists == 1, the four AP-index UFs
        # return valid indices forming a length-3 AP, pairwise distinct.
        ("ForAll(lambda G_mat, n_, M_arr: Implies("
         "is_matching(G_mat, n_, M_arr) == 1 and "
         "find_aug3_exists(G_mat, n_, M_arr) == 1, "
         "0 <= find_aug3_u(G_mat, n_, M_arr) and find_aug3_u(G_mat, n_, M_arr) < n_ and "
         "0 <= find_aug3_v(G_mat, n_, M_arr) and find_aug3_v(G_mat, n_, M_arr) < n_ and "
         "0 <= find_aug3_z(G_mat, n_, M_arr) and find_aug3_z(G_mat, n_, M_arr) < n_ and "
         "0 <= find_aug3_w(G_mat, n_, M_arr) and find_aug3_w(G_mat, n_, M_arr) < n_ and "
         "find_aug3_u(G_mat, n_, M_arr) != find_aug3_v(G_mat, n_, M_arr) and "
         "find_aug3_u(G_mat, n_, M_arr) != find_aug3_z(G_mat, n_, M_arr) and "
         "find_aug3_u(G_mat, n_, M_arr) != find_aug3_w(G_mat, n_, M_arr) and "
         "find_aug3_v(G_mat, n_, M_arr) != find_aug3_z(G_mat, n_, M_arr) and "
         "find_aug3_v(G_mat, n_, M_arr) != find_aug3_w(G_mat, n_, M_arr) and "
         "find_aug3_z(G_mat, n_, M_arr) != find_aug3_w(G_mat, n_, M_arr)))"),

        # (A6) Applying the length-3 flip preserves is_matching.
        ("ForAll(lambda G_mat, n_, M_arr: Implies("
         "is_matching(G_mat, n_, M_arr) == 1 and "
         "find_aug3_exists(G_mat, n_, M_arr) == 1, "
         "is_matching(G_mat, n_, "
         "Update(Update(Update(Update(M_arr, "
         "find_aug3_u(G_mat, n_, M_arr), find_aug3_v(G_mat, n_, M_arr)), "
         "find_aug3_v(G_mat, n_, M_arr), find_aug3_u(G_mat, n_, M_arr)), "
         "find_aug3_z(G_mat, n_, M_arr), find_aug3_w(G_mat, n_, M_arr)), "
         "find_aug3_w(G_mat, n_, M_arr), find_aug3_z(G_mat, n_, M_arr))) == 1))"),

        # (A7) Same flip increments matching_size by 1.  (ranking-decrease closure)
        ("ForAll(lambda G_mat, n_, M_arr: Implies("
         "is_matching(G_mat, n_, M_arr) == 1 and "
         "find_aug3_exists(G_mat, n_, M_arr) == 1, "
         "matching_size(G_mat, n_, "
         "Update(Update(Update(Update(M_arr, "
         "find_aug3_u(G_mat, n_, M_arr), find_aug3_v(G_mat, n_, M_arr)), "
         "find_aug3_v(G_mat, n_, M_arr), find_aug3_u(G_mat, n_, M_arr)), "
         "find_aug3_z(G_mat, n_, M_arr), find_aug3_w(G_mat, n_, M_arr)), "
         "find_aug3_w(G_mat, n_, M_arr), find_aug3_z(G_mat, n_, M_arr))) == "
         "matching_size(G_mat, n_, M_arr) + 1))"),

        # (A8) Berge: no AP + is_matching → is_max.  Phrased with
        # `not (... == 1)` to match the framework's ¬g loop-exit form.
        ("ForAll(lambda G_mat, n_, M_arr: Implies("
         "is_matching(G_mat, n_, M_arr) == 1 and "
         "not (find_aug3_exists(G_mat, n_, M_arr) == 1), "
         "is_max_matching(G_mat, n_, M_arr) == 1))"),
    ],

    pre  = "n >= 0 and is_matching(G, n, M) == 1",
    post = "is_max_matching(G, n, M) == 1",

    atoms = {
        # SB(init): just a counter init; M is preserved (input
        # already a matching).
        "s@B0": [{"i": "0"}],

        "tau@L0": ["is_matching(G, n, M) == 1"],
        "g@L0":   ["find_aug3_exists(G, n, M) == 1"],
        "phi@L0": ["n - 2 * matching_size(G, n, M)"],

        # Body: parallel-dict transition.  Inline all four
        # `find_aug3_*` UF calls into the Update chain — every
        # RHS evaluates against the pre-state M, so all calls
        # see the same M reference.  Also increment counter i
        # (cosmetic; phi uses matching_size).
        "s@B1": [{
            "M": (
                "Update("
                "Update("
                "Update("
                "Update("
                "M, "
                "find_aug3_u(G, n, M), find_aug3_v(G, n, M)), "
                "find_aug3_v(G, n, M), find_aug3_u(G, n, M)), "
                "find_aug3_z(G, n, M), find_aug3_w(G, n, M)), "
                "find_aug3_w(G, n, M), find_aug3_z(G, n, M))"
            ),
            "i": "i + 1",
        }],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 1_800_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_aug3_flip_concrete"
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
