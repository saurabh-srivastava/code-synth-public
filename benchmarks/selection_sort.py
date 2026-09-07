"""selection_sort — Phase 3.Q: classic selection sort with sortedness post.

Pairs with `bubble_sort.py` to round out the sort family.  Different
inner-invariant shape: bubble sort's inner τ tracks "A[j] is the max
of A[0..j+1]"; selection sort's inner τ tracks "min_idx is the index
of the minimum in A[i..j]".

    i := 0
    while (i < n):
        min_idx := i;  j := i + 1
        while (j < n):
            if (A[j] < A[min_idx]):  min_idx := j;  j := j + 1
            else:                    j := j + 1
        # swap A[i] and A[min_idx]
        A := Update(Update(A, i, A[min_idx]), min_idx, A[i])
        i := i + 1
    // post: ∀p, q. 0 ≤ p ≤ q < n ⇒ A[p] ≤ A[q]

The inner Loop's body just updates `min_idx` and `j` — it does NOT
touch the array, so the inner inductive is array-Update-free.  The
array gets modified only by the outer body's SB3 (the swap).

Invariants
----------
`τ_outer` (after `i` outer iterations, the first `i` positions hold
the `i` smallest elements in sorted order, and the rest are ≥
everything in the prefix):

    ∀p, q. 0 ≤ p ≤ q < n ∧ p < i  ⇒  A[p] ≤ A[q]

This bilateral atom subsumes both "prefix sorted" (both p, q in
[0, i)) and "prefix ≤ rest" (p in [0, i), q in [i, n)).  Same trick
as bubble sort (REC 2 in template-reco.md).

`τ_inner`:
  - i < j ≤ n             (j ranges over the scan, starting at i+1)
  - i ≤ min_idx < j        (min_idx is a valid index in the scanned
                            portion)
  - i < n                  (outer guard preserved)
  - ∀k. i ≤ k < j ⇒ A[min_idx] ≤ A[k]    (min-index property)
  - outer suffix-dominance atom carried   (preserved by the inner
                                            loop, which doesn't
                                            touch A)

Spec:
    Pre  : n ≥ 0
    Post : ForAll(p, q: 0 ≤ p ≤ q < n  ⇒  A[p] ≤ A[q])
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(
        SB(n=1)                          # min_idx := i, j := i + 1
        >> Loop(SB(n=2))                 # inner: conditional min_idx update
        >> SB(n=1)                       # swap A[i], A[min_idx]
        >> SB(n=1)                       # i := i + 1
    ),
    inputs   = [Var("n", "int", "input"), Var("A", "int[]", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local"),
                Var("j", "int", "local"),
                Var("min_idx", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda p, q: Implies(0 <= p and p <= q and q < n, "
                "A[p] <= A[q]))"),

    atoms = {
        # SB0: i := 0.
        "s@B0":   [{"i": "0"}],

        # Outer τ.
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p <= q and q < n and p < i, "
             "A[p] <= A[q]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # SB1: min_idx := i; j := i + 1.
        "s@B1":   [{"min_idx": "i", "j": "i + 1"}],

        # Inner τ — min-index property + carried outer atom.
        "tau@L1": [
            "i < j",
            "j <= n",
            "i <= min_idx",
            "min_idx < j",
            "i < n",
            ("ForAll(lambda k: Implies("
             "i <= k and k < j, A[min_idx] <= A[k]))"),
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p <= q and q < n and p < i, "
             "A[p] <= A[q]))"),
        ],
        "g@L1":   ["j < n"],
        "phi@L1": ["n - j"],

        # Inner body SB(n=2): conditional min_idx update; both
        # branches advance j.
        "g@B2.0": ["A[j] < A[min_idx]"],
        "s@B2.0": [{"min_idx": "j", "j": "j + 1"}],
        "g@B2.1": ["A[j] >= A[min_idx]"],
        "s@B2.1": [{"j": "j + 1"}],

        # SB3: swap A[i] and A[min_idx].
        "s@B3":   [{"A": "Update(Update(A, i, A[min_idx]), min_idx, A[i])"}],

        # SB4: i := i + 1.
        "s@B4":   [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 1_800_000,   # 30 min
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
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
