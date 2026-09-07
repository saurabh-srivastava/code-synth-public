"""reverse_array — Phase X corpus benchmark.

In-place reverse of A[0..n) via two-pointer scan.  Loop swaps
A[lo] and A[hi], advancing both inward until lo >= hi.

Spec:
    Pre  : n >= 0 ∧ B is a ghost copy of A
    Post : ForAll k. 0 <= k < n ⇒ A[k] == B[n - 1 - k]
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "reverse the first n elements in place so that A[k] takes "
        "the old value of A[n - 1 - k] for every k in 0..n-1."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),  # ghost copy
                Var("n", "int", "input")],
    outputs  = [Var("A", "int[]", "output")],
    locals   = [Var("lo", "int", "local"),
                Var("hi", "int", "local")],

    pre      = ("(n >= 0) and "
                "ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))"),
    post     = ("ForAll(lambda k: Implies("
                "0 <= k and k < n, A[k] == B[n - 1 - k]))"),

    atoms = {
        # Init: lo := 0, hi := n - 1.
        "s@B0": [{"lo": "0", "hi": "n - 1"}],

        "tau@L0": [
            # Pointer invariants.
            "lo + hi == n - 1",
            "lo >= 0",
            "hi <= n - 1",
            # Bound on lo–hi spread (needed so ranking-LB
            # `hi - lo + 1 >= 0` holds at every τ state).
            "lo <= hi + 1",
            "n >= 0",
            # Reversed prefix matches B's suffix.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < lo, A[k] == B[n - 1 - k]))"),
            # Reversed suffix matches B's prefix.
            ("ForAll(lambda k: Implies("
             "hi < k and k < n, A[k] == B[n - 1 - k]))"),
            # Middle window still matches B.
            ("ForAll(lambda k: Implies("
             "lo <= k and k <= hi, A[k] == B[k]))"),
        ],
        "g@L0":   ["lo < hi"],
        # ranking must be ≥ 0 at every τ-consistent state, including
        # the n=0 entry state (lo=0, hi=-1).  `hi - lo + 1` is ≥ 0
        # there (= 0) and strictly decreases by 2 per iteration.
        "phi@L0": ["hi - lo + 1"],

        # Body: swap A[lo] and A[hi]; lo += 1; hi -= 1.
        "s@B1": [{
            "A": "Update(Update(A, lo, A[hi]), hi, A[lo])",
            "lo": "lo + 1",
            "hi": "hi - 1",
        }],
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
