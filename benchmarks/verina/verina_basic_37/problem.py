"""verina_basic_37 (findFirstOccurrence) — VERINA-basic port.

Given an array of integers sorted in non-decreasing order and a
target value, return the index of the FIRST occurrence of target,
or -1 if target does not occur.

VERINA spec (from datasets/verina/verina_basic_37/task.lean,
between the @start/@end markers; source of truth):
    signature : findFirstOccurrence (arr : Array Int) (target : Int) -> Int
    precond   : List.Pairwise (· ≤ ·) arr.toList
                (arr is sorted in non-decreasing order)
    code      : linear scan from i = 0; return i on arr[i] = target,
                return -1 on arr[i] > target (sorted early-exit),
                else advance; return -1 if the scan runs off the end.
    postcond  :
        (result = -1 ∨ result ≥ 0) ∧
        (result ≥ 0 →
           result.toNat < arr.size ∧
           arr[result.toNat]! = target ∧
           (∀ i, i < result.toNat → arr[i]! ≠ target)) ∧
        (result = -1 →
           (∀ i, i < arr.size → arr[i]! ≠ target))

Port / fidelity mapping
-----------------------
    A : int[]   = arr        (element arr[i] ↦ A[i])
    n : int     = arr.size   (VERINA `arr.size` is a Nat; passed as an
                              int input with the implicit n ≥ 0 stated
                              in `pre`).
    target : int = target    (already Int).
    res : int    = result    (already Int; sentinel -1 for "not found").

    Pre  : n >= 0
         ∧ ForAll(k: 0<=k ∧ k+1<n ⇒ A[k] <= A[k+1])
           — the standard non-decreasing encoding of VERINA's
             `List.Pairwise (· ≤ ·) arr.toList` (equivalent by
             transitivity of ≤).

    Post : (res == -1 or res >= 0)
         ∧ (res >= 0 ⇒ res < n ∧ A[res] == target
                       ∧ ForAll(k: 0<=k<res ⇒ A[k] != target))
         ∧ (res == -1 ⇒ ForAll(k: 0<=k<n ⇒ A[k] != target))

SPEC-FIDELITY NOTE
------------------
Our post is a direct transcription of VERINA's postcond.  Because
the returned index is non-negative in the "found" branch,
`result.toNat` collapses to `res` (Z3 int) and `result.toNat < arr.size`
becomes `res < n`; the "not found → absent everywhere" clause and the
"found → first occurrence" clause (∀ k < res. A[k] ≠ target) transcribe
one-for-one.  VERINA's `∀ i : Nat, i < …` universals carry an implicit
i ≥ 0 (Nat index); we add the explicit `0 <= k` lower bound, a no-op for
the never-reached k < 0.  The precond `List.Pairwise (· ≤ ·)` is written
as adjacent-pair non-decreasing, equivalent to the pairwise-all form by
transitivity of ≤.  So our (pre, post) is faithful to VERINA's.

ALGORITHM the synthesizer picks
-------------------------------
A single left-to-right scan.  Because we visit indices in increasing
order and stop at the first hit, the returned index is automatically
the FIRST occurrence — the sortedness precondition is therefore not
even required for correctness of this (fully general) linear scan;
it is carried only to stay faithful to VERINA's precond.

    i := 0;
    while (i < n and A[i] != target):   # skip the non-target prefix
        i := i + 1;
    if i >= n:  res := -1                # ran off the end: absent
    else:       res := i                 # A[i] == target: first hit

Loop invariant (tau@L0):
    0 <= i <= n
  ∧ n >= 0
  ∧ ForAll(k: 0<=k<i ⇒ A[k] != target)   (prefix has no target)
At loop exit the guard gives (i >= n) ∨ (A[i] == target); combined with
i <= n and the prefix invariant this discharges both post branches:
  - i >= n ⇒ i == n ⇒ ∀k<n. A[k] != target  (res = -1 clause);
  - i <  n ⇒ A[i] == target ∧ ∀k<i. A[k] != target  (first-occurrence).

TRUST SURFACE: none beyond Z3.  No uninterpreted function, no axioms,
no Lean dispatch — the invariant is expressible with quantified tau
atoms, so Z3 discharges every obligation (init / inductive / coverage /
termination / post).  Same family as corpus `find_first_pos`
(first-witness scan) and `verina_basic_24` (scan + final SB(n=2) map).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of size n sorted in non-decreasing "
        "order and a target value, return the index of the first "
        "occurrence of target in A[0..n), or -1 if target is absent."
    ),

    template = SB() >> Loop(SB()) >> SB(n=2),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("target", "int", "input")],
    outputs  = [Var("res", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre = (
        "n >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k + 1 < n, "
        "A[k] <= A[k + 1]))"
    ),
    post = (
        "(res == -1 or res >= 0) and "
        "Implies(res >= 0, "
        "  (res < n) and (A[res] == target) and "
        "  ForAll(lambda k: Implies(0 <= k and k < res, "
        "  A[k] != target))) and "
        "Implies(res == -1, "
        "  ForAll(lambda k: Implies(0 <= k and k < n, "
        "  A[k] != target)))"
    ),

    atoms = {
        # Init: start the scan at index 0.
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # Prefix [0, i) contains no occurrence of target.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] != target))"),
        ],
        # Continue while in bounds AND current element is not target.
        "g@L0":   ["(i < n) and (A[i] != target)"],
        "phi@L0": ["n - i"],

        # Loop body: advance the scan.
        "s@B1": [{"i": "i + 1"}],

        # Final SB(n=2): map scan outcome to the result.
        # Branch 0: ran off the end (i == n) → not found → -1.
        "g@B2.0": ["i >= n"],
        "s@B2.0": [{"res": "-1"}],
        # Branch 1: stopped in bounds (A[i] == target) → first hit i.
        "g@B2.1": ["i < n"],
        "s@B2.1": [{"res": "i"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/verina_basic_37_findFirstOccurrence"),
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
