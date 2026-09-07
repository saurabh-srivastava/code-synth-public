"""fibonacci_array — self-referential array recurrence benchmark.

Produce an integer array C of length n where C[k] == fib(k) for all
0 <= k < n.  The Fibonacci recurrence is supplied as three axioms over
an uninterpreted symbol `fib`.

Algorithm:
    C := Update(C, 0, 0); C := Update(C, 1, 1); i := 2;
    while (i < n):
        C := Update(C, i, C[i-1] + C[i-2]);
        i := i + 1;

Spec (restricted to n >= 2 to avoid the boundary where the two-element
base case can over-write past the requested length; the spec is
vacuous for n == 0 and equivalent to "C[0] == 0" for n == 1, both of
which the init SB already satisfies, but a single-Pre branch simplifies
the obligation set):

    Pre  : n >= 2
    Post : ForAll k. 0 <= k < n ⇒ C[k] == fib(k)

The HARD aspects:
  - **Self-referential reads**: the loop body's RHS reads C[i-1] and
    C[i-2] from the SAME array being written.  The inductive must
    track the prefix invariant `C[k] == fib(k)` for k < i so the
    reads are well-defined.
  - **Two-element base case**: i starts at 2, and the loop guard is
    i < n.  The entry-bundle τ has to discharge C[0] == fib(0) AND
    C[1] == fib(1) directly from the user axioms (sc0 UF cliff).
  - **UF + two-step recurrence**: fib(k+2) = fib(k+1) + fib(k) has
    TWO prior values; the inductive case rewrites the body's
    Update against the recurrence at k = i - 2.

Curated `.solved.lean` companions live under
`lean/SynthLean/Y2Corpus/fibonacci_array/`.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer n with n >= 2 and an integer array C of "
        "length at least n, set C[k] := fib(k) for every k in 0..n-1, "
        "where fib is the Fibonacci sequence (fib(0)=0, fib(1)=1, "
        "fib(k+2)=fib(k+1)+fib(k))."
    ),

    template = SB() >> Loop(SB()) >> SB(),
    inputs   = [Var("C", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("C", "int[]", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [("fib", ["int"], "int")],
    axioms = [
        "fib(0) == 0",
        "fib(1) == 1",
        ("ForAll(lambda k: Implies(k >= 0, "
         "fib(k + 2) == fib(k + 1) + fib(k)))"),
    ],

    pre  = "n >= 2",
    post = ("ForAll(lambda k: Implies(0 <= k and k < n, "
            "C[k] == fib(k)))"),

    atoms = {
        # Init: C[0] := 0; C[1] := 1; i := 2.
        # Single parallel assignment (chain-aware Lean translator
        # requires dict-shape atoms for SB chain items).  The two
        # writes nest via Update(Update(C, 0, 0), 1, 1).
        "s@B0": [{"C": "Update(Update(C, 0, 0), 1, 1)", "i": "2"}],

        "tau@L0": [
            "2 <= i",
            "i <= n",
            ("ForAll(lambda k: Implies(0 <= k and k < i, "
             "C[k] == fib(k)))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Body: C[i] := C[i-1] + C[i-2]; i := i + 1.
        "s@B1": [{"C": "Update(C, i, C[i - 1] + C[i - 2])",
                  "i": "i + 1"}],

        "s@B2": [ {} ],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/fibonacci_array",
    solver_timeout_ms = 900_000,
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
