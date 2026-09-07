"""bench_aug_path_max — C1.D K.3.0: maximum matching via Berge (axiomatized AP).

The first L1.6 benchmark to use a MAXIMUM-MATCHING post (not
maximal, not count-bounded).  The body's augmentation step is
axiomatized as a UF; the framework synthesizes the OUTER LOOP
that iterates "while AP exists, augment."  Berge's theorem
closes the loop's exit case: no AP → maximum.

Algorithm shape — Edmonds-Karp / Hopcroft-Karp outer loop:

  M := empty_matching;
  while exists_aug_path(G, n, M) == 1:
      M := step_augment(G, n, M);

  post: is_max_matching(G, n, M) == 1

Slice A pattern: UFs are opaque with axiomatic semantics; the
synthesizer picks the loop shape + ranking; the body is the UF.

== Termination ranking ==

Each augmentation increases matching size by 1.  Matching size
is bounded by n/2.  Use phi = `n - 2*matching_size(G, n, M)`:
  - phi ≥ 0 from `matching_size_bounded` axiom (2*ms ≤ n).
  - phi strict-decreases by 2 from `step_augment_increment`
    axiom (ms(step_augment(M)) = ms(M) + 1).

No local counter `i` needed.  The loop terminates by Lean's
well-foundedness via the UF-backed phi.

== What this validates ==

Berge's theorem (`Berge_no_aug_path_max` in Matching.lean) is
the key to expressing maximum matching declaratively.  The
framework synthesizes a loop that terminates at no-AP, then
Berge converts no-AP → max.

What this does NOT do: implement augmenting-path detection.
`step_augment` is a UF.  C1.D's full picture (K.3.2+)
requires concrete AP detection, which is multi-week.

Observed (2026-05-24, 15s): 1 solution, score 14.50.  No
Tier-3 helpers needed — the framework's generic Lean tactic
chain dispatches all 5 constraints via the 6-axiom chain
(empty-matching valid + matching-size non-neg + matching-size
bounded + step preserves matching + step increments
matching-size + Berge).  First L1.6 benchmark with a TRUE
maximum-matching post.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("M", "int", "output")],
    locals   = [],

    uninterpreted = [
        ("is_matching",     ["int", "int", "int"], "int"),
        ("is_max_matching", ["int", "int", "int"], "int"),
        ("exists_aug_path", ["int", "int", "int"], "int"),
        ("matching_size",   ["int", "int", "int"], "int"),
        ("empty_matching",  [],                    "int"),
        ("step_augment",    ["int", "int", "int"], "int"),
    ],

    axioms = [
        # (A1) Empty matching is a valid matching.
        "ForAll(lambda G_, n_: is_matching(G_, n_, empty_matching()) == 1)",

        # (A2) matching_size is non-negative.
        "ForAll(lambda G_, n_, M_: matching_size(G_, n_, M_) >= 0)",

        # (A3) matching_size is bounded by n/2 (well-defined matchings have
        # at most n/2 pairs).  Equivalent to 2*ms <= n.
        ("ForAll(lambda G_, n_, M_: Implies("
         "is_matching(G_, n_, M_) == 1, "
         "2 * matching_size(G_, n_, M_) <= n_))"),

        # (A4) step_augment preserves is_matching.
        ("ForAll(lambda G_, n_, M_: Implies("
         "is_matching(G_, n_, M_) == 1 and exists_aug_path(G_, n_, M_) == 1, "
         "is_matching(G_, n_, step_augment(G_, n_, M_)) == 1))"),

        # (A5) step_augment increments matching_size by 1.
        ("ForAll(lambda G_, n_, M_: Implies("
         "is_matching(G_, n_, M_) == 1 and exists_aug_path(G_, n_, M_) == 1, "
         "matching_size(G_, n_, step_augment(G_, n_, M_)) == "
         "matching_size(G_, n_, M_) + 1))"),

        # (A6) Berge's theorem forward: no AP + is_matching → is_max.
        # Phrased with `not (... == 1)` to match the framework's loop-
        # exit ¬g form `¬(exists_aug_path == 1)`.  Avoids the
        # Int-valued-bool gap where Lean can't bridge ¬(x==1) to x==0.
        ("ForAll(lambda G_, n_, M_: Implies("
         "is_matching(G_, n_, M_) == 1 and "
         "not (exists_aug_path(G_, n_, M_) == 1), "
         "is_max_matching(G_, n_, M_) == 1))"),
    ],

    pre  = "n >= 0",
    post = "is_max_matching(G, n, M) == 1",

    atoms = {
        "s@B0":   [{"M": "empty_matching()"}],
        "tau@L0": ["is_matching(G, n, M) == 1"],
        "g@L0":   ["exists_aug_path(G, n, M) == 1"],
        "phi@L0": ["n - 2 * matching_size(G, n, M)"],
        "s@B1":   [{"M": "step_augment(G, n, M)"}],
    },
    max_solutions = 1,
    expected_solutions = None,
    expected_lean_hits = None,
    solver_timeout_ms = 600_000,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/l16_aug_path_max"
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
