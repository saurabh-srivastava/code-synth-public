"""verina_basic_51 — BinarySearch (insertion index in a sorted array).

Port of VERINA-basic task `verina_basic_51` (upstream: Clover
`Clover_binary_search`).  Given a non-decreasing integer array `a`
and a target `key`, return the insertion index `n`: the first
position such that everything before it is strictly less than
`key` and everything from it onward is `>= key`.  If `key` exceeds
all elements, return `a.size`.

The VERINA reference code is a bona-fide binary search
(`binarySearchLoop` narrowing `[lo, hi)` by midpoints).  We are
NOT required to reproduce the O(log n) algorithm — only to
synthesize *some* program that meets the same postcondition.  The
synthesizer picks the O(n) linear-scan witness of the SAME
insertion index:

    idx := 0;
    while (idx < n and A[idx] < key):   // early-exit guard
        idx := idx + 1;
    return idx;

Both programs compute the identical mathematical function (the
first index whose element is `>= key`); the postcondition pins
that index uniquely, so the linear scan is a faithful realization
of the spec.  (cf. `find_first_pos` for the early-exit shape,
`verina_basic_46_lastPosition` for the sorted-array search port.)

This is a search / witness benchmark (index-returning), so it is
PURE Z3 with quantified tau atoms — no uninterpreted functions,
no Lean dispatch (cf. `min_index`, `find_first_pos`,
`verina_basic_46_lastPosition`).  Unlike lastPosition, the
sortedness precondition IS load-bearing here: the "drop-suffix all
>= key" postcondition clause is only provable because monotonicity
lets A[idx] >= key propagate to every later index.

-----------------------------------------------------------------
VERINA fidelity mapping
-----------------------------------------------------------------
  a : Array Int            -> A : int[]   (input)
  key : Int                -> key : int   (input)
  a.size (a Nat)           -> n : int     (input, with n >= 0)
  return : Nat             -> idx : int   (output, with idx >= 0)

VERINA precond:
    List.Pairwise (· ≤ ·) a.toList
      -> "sorted non-decreasing".  Pairwise(≤) on the list means
         exactly ∀ p q. 0 <= p <= q < n ⇒ A[p] <= A[q] (the
         monotone / transitive-closure form).  We encode that
         two-variable form directly (faithful — it IS what
         Pairwise(≤) denotes, and it is the form the proof needs).

VERINA postcond (over result idx, an Array.size-bounded Nat):
    result ≤ a.size                                        [P1]
    ∧ (a.take result).all (fun x => x < key)               [P2]
    ∧ (a.drop result).all (fun x => x ≥ key)               [P3]

  mapped 1:1 to our `post`:
    P1 : (0 <= idx) and (idx <= n)
           -- idx >= 0 is the Nat implicit; idx <= n is `≤ a.size`.
    P2 : ForAll k. 0 <= k < idx ⇒ A[k] < key
           -- `take idx` is exactly the index range [0, idx).
           -- (subsumes the description's "if idx = size, all < key".)
    P3 : ForAll k. idx <= k < n ⇒ A[k] >= key
           -- `drop idx` is exactly the index range [idx, n).

  Faithful capture: take/drop `.all` predicates translate directly
  to the two half-open index ranges split at the returned index.

-----------------------------------------------------------------
Loop invariant (over the scanned prefix [0, idx))
-----------------------------------------------------------------
  I1: 0 <= idx <= n                     -- idx stays in range.
  I2: sortedness carried into the loop  -- available at exit for P3.
  I3: ForAll k. 0 <= k < idx ⇒ A[k] < key
        -- every scanned element is strictly below key.

  At exit the guard is false: idx >= n  OR  A[idx] >= key.
    P1  <- I1.
    P2  <- I3 directly.
    P3  <- for k in [idx, n):
             if idx >= n the range is empty (I1 gives idx == n);
             else A[idx] >= key, and sortedness (I2) at (idx, k)
             gives A[k] >= A[idx] >= key.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-decreasing integer array A of length n "
        "(n >= 0) and a target key, return the first insertion "
        "index idx in [0, n] such that every element before idx "
        "is < key and every element from idx onward is >= key."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("key", "int", "input")],
    outputs  = [Var("idx", "int", "output")],

    # VERINA precond: Pairwise(≤) == monotone (two-variable) form.
    # Load-bearing for the drop-suffix clause (P3).
    pre = (
        "(n >= 0) and "
        "ForAll(lambda p, q: Implies("
        "  0 <= p and p <= q and q < n, A[p] <= A[q]))"
    ),

    # VERINA postcond, mapped 1:1 (see docstring).
    post = (
        "(0 <= idx) and (idx <= n) and "
        "ForAll(lambda k: Implies(0 <= k and k < idx, "
        "                         A[k] < key)) and "
        "ForAll(lambda k: Implies(idx <= k and k < n, "
        "                         A[k] >= key))"
    ),

    atoms = {
        # Init: idx := 0.
        "s@B0": [{"idx": "0"}],

        "tau@L0": [
            "0 <= idx",
            "idx <= n",
            "n >= 0",
            # Sortedness carried into the loop (needed at exit for P3).
            ("ForAll(lambda p, q: Implies("
             " 0 <= p and p <= q and q < n, A[p] <= A[q]))"),
            # Scanned prefix is strictly below key.
            ("ForAll(lambda k: Implies("
             " 0 <= k and k < idx, A[k] < key))"),
        ],
        # Early-exit guard: keep scanning while in range AND the
        # current element is still below key.
        "g@L0":   ["(idx < n) and (A[idx] < key)"],
        "phi@L0": ["n - idx"],

        # Body: advance the scan cursor.
        "s@B1": [{"idx": "idx + 1"}],
    },

    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_51/lean/SynthLean/Y2Corpus/verina_basic_51",
    wedge_threshold = 200,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    print(f"wall: {time.monotonic() - t:.1f}s")
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
