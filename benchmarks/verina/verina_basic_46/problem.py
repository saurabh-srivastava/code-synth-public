"""verina_basic_46 — lastPosition (last occurrence in a sorted array).

Port of VERINA-basic task `verina_basic_46` (upstream:
dafny-synthesis task_id_793).  Find the index of the LAST
occurrence of `elem` in a non-decreasing array `arr`, or -1 if
`elem` is absent.  The reference code is a full linear scan that
records the most-recent matching index:

    pos := -1; i := 0;
    while (i < n):
        if A[i] == elem:  pos := i;   // remember last match
        i := i + 1;
    return pos;

Note: the algorithm does NOT exploit sortedness — it scans the
whole array.  The sortedness precondition is carried faithfully
(see fidelity note) but is unused by the correctness proof.

This is a search / witness benchmark (index-returning), so it is
PURE Z3 with quantified tau atoms — no uninterpreted functions,
no Lean dispatch (cf. `min_index`, `find_first_pos`,
`all_positive`, `is_sorted`).

-----------------------------------------------------------------
VERINA fidelity mapping
-----------------------------------------------------------------
  arr : Array Int          -> A : int[]   (input)
  elem : Int               -> elem : int  (input)
  arr.size (a Nat)         -> n : int      (input, with n >= 0)
  return : Int             -> pos : int    (output)

VERINA precond:
    List.Pairwise (· ≤ ·) arr.toList
      -> "sorted non-decreasing", encoded as the adjacent form
         ForAll k. 0 <= k < n-1 ⇒ A[k] <= A[k+1]
         (equivalent to Pairwise(≤) since ≤ is transitive on a
          list; faithful).  UNUSED by the proof.

VERINA postcond (over result r):
    (r = -1 ∨ r ≥ 0)                                        [P1]
    ∧ (r ≥ 0 →
         r.toNat < arr.size                                 [P2a]
         ∧ arr[r.toNat]! = elem                             [P2b]
         ∧ (arr.toList.drop (r.toNat + 1)).all (· ≠ elem))  [P2c]
    ∧ (r = -1 → arr.toList.all (· ≠ elem))                  [P3]

  mapped 1:1 to our `post`:
    P1  : pos == -1 or pos >= 0
    P2  : Implies(pos >= 0,
              pos < n                                        (P2a)
              and A[pos] == elem                             (P2b)
              and ForAll k. pos < k < n ⇒ A[k] != elem)      (P2c)
                 -- `drop(pos+1).all(≠elem)` == "every index
                 --  strictly greater than pos is not elem"
    P3  : Implies(pos == -1,
              ForAll k. 0 <= k < n ⇒ A[k] != elem)

  This is a faithful capture: P2c's `drop(pos+1).all(≠elem)`
  is exactly "no index > pos holds elem", which pins pos to the
  LAST occurrence.

-----------------------------------------------------------------
Loop invariant (over the scanned prefix [0, i))
-----------------------------------------------------------------
  I1: pos == -1  or  (0 <= pos and pos < i and A[pos] == elem)
        -- pos is a valid matched index in the scanned prefix.
  I2: ForAll k. pos < k < i ⇒ A[k] != elem
        -- nothing strictly after pos (within the prefix) matches.
        -- when pos == -1 this reads "no index in [0,i) matches",
           unifying the found / not-found cases in one atom.

  At exit i == n:
    I1 gives P1 and (under pos>=0) P2a/P2b;
    I2 gives P2c (pos>=0 case) and P3 (pos==-1 case).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given a non-decreasing integer array A of length n "
        "(n >= 0) and a target elem, return the index of the "
        "last occurrence of elem in A[0..n), or -1 if elem does "
        "not occur."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("elem", "int", "input")],
    outputs  = [Var("pos", "int", "output")],
    locals   = [Var("i", "int", "local")],

    # VERINA precond: sorted non-decreasing (adjacent form).
    # Unused by the proof but carried for fidelity.
    pre = (
        "n >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k < n - 1, "
        "A[k] <= A[k + 1]))"
    ),

    # VERINA postcond, mapped 1:1 (see docstring).
    post = (
        "(pos == -1 or pos >= 0) and "
        "Implies(pos >= 0, "
        "  (pos < n) and (A[pos] == elem) and "
        "  ForAll(lambda k: Implies(pos < k and k < n, "
        "                           A[k] != elem))) and "
        "Implies(pos == -1, "
        "  ForAll(lambda k: Implies(0 <= k and k < n, "
        "                           A[k] != elem)))"
    ),

    atoms = {
        # Init: pos := -1, i := 0.
        "s@B0": [{"pos": "-1", "i": "0"}],

        "tau@L0": [
            # I1: pos is a valid matched index in prefix [0, i).
            "pos == -1 or (0 <= pos and pos < i and A[pos] == elem)",
            # I2: no index strictly after pos (within [0, i)) matches.
            ("ForAll(lambda k: Implies(pos < k and k < i, "
             "A[k] != elem))"),
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] == elem → remember this index, advance.
        "g@B1.0": ["A[i] == elem"],
        "s@B1.0": [{"pos": "i", "i": "i + 1"}],
        # Branch 1: A[i] != elem → just advance.
        "g@B1.1": ["A[i] != elem"],
        "s@B1.1": [{"i": "i + 1"}],

        # Final SB: no-op (pos already holds the result).
        "s@B2": [{}],
    },

    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_46/lean/SynthLean/Y2Corpus/verina_basic_46",
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
