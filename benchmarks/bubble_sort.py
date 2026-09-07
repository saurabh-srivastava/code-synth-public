"""bubble_sort — Phase 3.P: optimized bubble sort with sortedness post.

The big one — nested loops + bilateral-quantified array invariants
on the inductive constraint, all in BOTH position.  This is the
canonical "real sort" benchmark; succeeding here would validate the
framework on a tier-1 verification problem.

    i := 0
    while (i < n):
        j := 0
        while (j < n - 1 - i):
            if (A[j] > A[j+1]):
                A := Update(Update(A, j, A[j+1]), j+1, A[j])   // swap
                j := j + 1
            else:
                j := j + 1
        i := i + 1
    // post: ∀p, q. 0 ≤ p ≤ q < n ⇒ A[p] ≤ A[q]

Optimization: inner bound `j < n - 1 - i` shrinks each pass — the
last `i` elements are already sorted in their final positions, so
the inner loop stops before touching them.  Without this, the inner
swap could disturb the sorted suffix.

The conditional swap is folded into a SB(n=2) where BOTH branches
also increment j; this keeps the inner Loop body as a single SB
(no Phase 3.K recursion at the inner level).

Invariants
----------
`τ_outer`: after `i` outer iterations, the suffix `A[n-i .. n-1]`
is sorted AND ≥ every element in the prefix `A[0 .. n-i-1]`.  A
single bilateral atom captures both:
    ∀p, q. 0 ≤ p ≤ q < n ∧ q ≥ n-i  ⇒  A[p] ≤ A[q]
(p in prefix, q in suffix → dominance; both in suffix → sortedness.)

`τ_inner`: outer invariants preserved + the "bubble" property —
A[j] is the maximum of A[0..j+1].  Combined with dominance at the
inner exit (j = n-1-i), this gives `A[n-1-i]` ≥ everything in
[0, n-i), which is exactly what's needed to extend the sorted
suffix to `[n-i-1, n-1]` after the outer step `i := i + 1`.

Spec:
    Pre  : n ≥ 0
    Post : ForAll(p, q: 0 ≤ p ≤ q < n  ⇒  A[p] ≤ A[q])
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1) >> Loop(SB(n=2)) >> SB(n=1)),
    inputs   = [Var("n", "int", "input"), Var("A", "int[]", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("i", "int", "local"), Var("j", "int", "local")],
    pre      = "n >= 0",
    post     = ("ForAll(lambda p, q: Implies(0 <= p and p <= q and q < n, "
                "A[p] <= A[q]))"),

    atoms = {
        # SB0: i := 0.
        "s@B0": [{"i": "0"}],

        # Outer τ.
        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p <= q and q < n and q >= n - i, "
             "A[p] <= A[q]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # SB1: j := 0.
        "s@B1":   [{"j": "0"}],

        # Inner τ.  The bubble property `A[k] <= A[j]` for k ≤ j is
        # the crux of bubble sort.
        "tau@L1": [
            "0 <= j",
            "j <= n - 1 - i",
            "i < n",
            "n >= 0",
            ("ForAll(lambda p, q: Implies("
             "0 <= p and p <= q and q < n and q >= n - i, "
             "A[p] <= A[q]))"),
            ("ForAll(lambda k: Implies("
             "0 <= k and k <= j, A[k] <= A[j]))"),
        ],
        "g@L1":   ["j < n - 1 - i"],
        "phi@L1": ["n - 1 - i - j"],

        # Inner body SB(n=2): conditional swap, both branches j := j+1.
        "g@B2.0": ["A[j] > A[j+1]"],
        "s@B2.0": [{
            "A": "Update(Update(A, j, A[j+1]), j+1, A[j])",
            "j": "j + 1",
        }],
        "g@B2.1": ["A[j] <= A[j+1]"],
        "s@B2.1": [{"j": "j + 1"}],

        # SB3: i := i + 1.
        "s@B3":   [{"i": "i + 1"}],
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
