"""verina_basic_29 (removeElement) — VERINA-basic port.

Remove the element at index k from array s, shifting everything
after k left by one.  The output is one element shorter than the
input.  A per-element conditional inside a single loop: for output
index i, copy s[i] when i < k, otherwise copy s[i+1].  Same shape
family as `clamp_array_positive` (SB() >> Loop(SB(n=2)) >> SB() with
a 2-way branch in the loop body), but the branch predicate is on the
index (i < k) rather than on the element value.

VERINA source (source of truth):
  signature : removeElement (s : Array Int) (k : Nat) -> Array Int
  precond   : k < s.size
  code      : s.eraseIdx! k
  postcond  : result.size = s.size - 1 ∧
              (∀ i, i < k → result[i]! = s[i]!) ∧
              (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)

Fidelity mapping:
  - VERINA `s : Array Int`      -> our input array A + length n (= s.size).
  - VERINA `k : Nat`            -> our int input k, with implied k >= 0.
  - VERINA `result : Array Int` -> our output array B (= result), whose
                                   logical size is n - 1.
  - VERINA precond `k < s.size` -> our pre `(0 <= k) and (k < n)`.  The
                                   `0 <= k` conjunct is the Nat-ness of k
                                   (VERINA's k : Nat); `k < n` is the
                                   literal precond.  Together they imply
                                   n >= 1, so the output size n-1 >= 0.
  - VERINA `result.size = s.size - 1`
                                -> B has logical length n-1 by construction:
                                   the loop writes B[0..n-1) and the post's
                                   quantifiers range over exactly [0, n-1).
                                   NOTE: our arrays are unbounded Z3 maps
                                   with size carried as the separate int
                                   `n`; the `.size` equality is captured
                                   structurally (quantifier ranges), not as
                                   a first-class array-length fact.  This is
                                   the standard array-model fidelity gap
                                   shared by every array benchmark in the
                                   corpus.
  - VERINA `∀ i < k, result[i]! = s[i]!`
                                -> ForAll j. 0<=j<k => B[j] == A[j].
  - VERINA `∀ i < result.size, i >= k -> result[i]! = s[i+1]!`
                                -> ForAll j. k<=j<n-1 => B[j] == A[j+1].

No auxiliary fold/sum/count function is referenced by the postcond,
so this is a PURE Z3 benchmark (no UF, no axioms).  The invariant is
the standard "prefix-done" split, but with two clauses because the
copy source changes at the removed index k.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n, an output integer array "
        "B, and an index k (with 0 <= k < n), populate B with A's "
        "elements with the element at index k removed: B[j] = A[j] for "
        "j in [0, k), and B[j] = A[j+1] for j in [k, n-1).  B has "
        "logical length n-1."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input"),
                Var("k", "int", "input")],
    outputs  = [Var("B", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "(0 <= k) and (k < n)",
    post     = (
        "ForAll(lambda j: Implies(0 <= j and j < k, B[j] == A[j])) and "
        "ForAll(lambda j: Implies(k <= j and j < n - 1, B[j] == A[j + 1]))"
    ),

    atoms = {
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n - 1",
            "0 <= k",
            "k < n",
            # Prefix [0, i) below the removed index copies A directly.
            ("ForAll(lambda j: Implies("
             "0 <= j and j < i and j < k, B[j] == A[j]))"),
            # Prefix [0, i) at-or-above the removed index copies A shifted.
            ("ForAll(lambda j: Implies("
             "k <= j and j < i, B[j] == A[j + 1]))"),
        ],
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - 1 - i"],

        # Loop body: SB(n=2)
        # Branch 0: i < k  -> B[i] := A[i]     (below removed index)
        "g@B1.0": ["i < k"],
        "s@B1.0": [{"B": "Update(B, i, A[i])", "i": "i + 1"}],
        # Branch 1: i >= k -> B[i] := A[i + 1] (at/above removed index)
        "g@B1.1": ["i >= k"],
        "s@B1.1": [{"B": "Update(B, i, A[i + 1])", "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_29/lean/SynthLean/Y2Corpus/verina_basic_29",
    wedge_threshold = 200,
    solver_timeout_ms = 120_000,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
