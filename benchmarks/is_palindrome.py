"""is_palindrome — Phase X corpus benchmark.

Check whether A[0..n) reads the same forwards and backwards
(A[k] == A[n - 1 - k] for all 0 ≤ k < n).  Two-pointer scan:
i starts at 0, j starts at n - 1, both advance toward the
middle; flag flips to 0 on any mismatch.

Spec:
    Pre  : n >= 0
    Post : (result == 1 ∧ ∀k. 0 ≤ k < n ⇒ A[k] == A[n - 1 - k])
         ∨ (result == 0 ∧ ∃k. 0 ≤ k < n ∧ A[k] != A[n - 1 - k])

Distinctive structural feature (vs is_sorted / all_positive):
  - TWO indices moving in OPPOSITE directions (i++ / j--).
  - Loop guard is `i < j` (convergence), not `i < n`.
  - Ranking is `j - i + 1`, decreasing by 2 per iteration
    (NOT the typical `n - i`).
  - τ ties the pointers via `i + j == n - 1` (mirrors
    reverse_array's `lo + hi == n - 1`), so the prefix-only
    flag-fold atom `∀k. 0 ≤ k < i ⇒ A[k] == A[n - 1 - k]`
    suffices to derive the full ∀k. 0 ≤ k < n ⇒ ... at exit
    (the upper window k ∈ (j, n - 1] is the symmetric mirror
    of [0, i)).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "return 1 if A[k] == A[n - 1 - k] for every k in 0..n - 1 "
        "(i.e. A is a palindrome on its first n elements), "
        "otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local"),
                Var("j", "int", "local")],

    pre      = "n >= 0",
    post     = (
        "((result == 1) and "
        " ForAll(lambda k: Implies("
        "0 <= k and k < n, A[k] == A[n - 1 - k]))) or "
        "((result == 0) and "
        " Exists(lambda k: 0 <= k and k < n and A[k] != A[n - 1 - k]))"
    ),

    atoms = {
        # Init: flag := 1, i := 0, j := n - 1.
        "s@B0": [{"flag": "1", "i": "0", "j": "n - 1"}],

        "tau@L0": [
            # Pointer relation — mirrors reverse_array's
            # `lo + hi == n - 1`.  With this, j == n - 1 - i,
            # so the prefix [0, i) and the suffix (j, n - 1]
            # mirror each other through k ↔ n - 1 - k.
            "i + j == n - 1",
            "i >= 0",
            "j <= n - 1",
            # Bound on i–j spread (needed so ranking-LB
            # `j - i + 1 >= 0` holds at every τ-consistent state,
            # including the n=0 entry state (i=0, j=-1)).
            "i <= j + 1",
            "n >= 0",
            # Flag-fold: matched prefix invariant.  Note the
            # range is [0, i) — by the pointer relation, this
            # also pins down the mirror suffix (n - 1 - k for
            # k ∈ [0, i) ranges over (j, n - 1]).  At loop exit
            # (i >= j ∧ i <= j + 1) the prefix [0, i) together
            # with its mirror covers all of [0, n).
            ("((flag == 1) and "
             " ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] == A[n - 1 - k]))) or "
             "((flag == 0) and "
             " Exists(lambda k: 0 <= k and k < n and A[k] != A[n - 1 - k]))"),
        ],
        "g@L0":   ["i < j"],
        # Two-pointer ranking: decreases by 2 per iteration,
        # ≥ 0 when i <= j + 1 (mirrors reverse_array).
        "phi@L0": ["j - i + 1"],

        # Branch 0: A[i] == A[j] → flag stays, advance both pointers.
        "g@B1.0": ["A[i] == A[j]"],
        "s@B1.0": [{"i": "i + 1", "j": "j - 1"}],
        # Branch 1: A[i] != A[j] → flag := 0, advance both pointers.
        "g@B1.1": ["A[i] != A[j]"],
        "s@B1.1": [{"flag": "0", "i": "i + 1", "j": "j - 1"}],

        # Final: result := flag.
        "s@B2": [{"result": "flag"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,
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
