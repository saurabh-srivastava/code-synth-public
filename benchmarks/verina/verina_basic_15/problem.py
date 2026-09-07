"""verina_basic_15 — containsConsecutiveNumbers.

Ported from VERINA-basic task `verina_basic_15`
(upstream: dafny-synthesis task_id_472).

VERINA signature:
    containsConsecutiveNumbers (a : Array Int) : Bool

VERINA precond:
    True   (no preconditions; array may be empty or non-empty)

VERINA postcond (source of truth):
    (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result

i.e. `result` is true iff the array contains at least one adjacent
pair (a[i], a[i+1]) with a[i] + 1 == a[i+1].

── Fidelity mapping ────────────────────────────────────────────────
  - `a : Array Int`  → our `A : int[]` plus a length `n : int`
    (the standard A + n modelling used throughout the corpus).
  - Nat `a.size`     → `n` with the implied `n >= 0` precondition.
  - Bool `result`    → int `result` in {0, 1}  (1 ≡ true, 0 ≡ false).
  - VERINA's `i < a.size - 1` (Nat subtraction, truncates to 0 when
    a.size == 0) ↔ our `k < n - 1` with `0 <= k`.  For n ∈ {0, 1}
    both give the empty range, so the empty/singleton array yields
    result 0 in both worlds — faithful.
  - VERINA's `a[i]! + 1 = a[i + 1]!` ↔ our `A[k] + 1 == A[k + 1]`.

Our post is the ↔ unrolled over the two Boolean values of result:
    (result == 1 ∧ ∃k. 0≤k<n-1 ∧ A[k]+1 == A[k+1])
  ∨ (result == 0 ∧ ∀k. 0≤k<n-1 ⇒ A[k]+1 != A[k+1])
which is exactly `(∃ …) ↔ (result == 1)`.

── Shape ───────────────────────────────────────────────────────────
Existential/flag-fold search — PURE Z3 with quantified τ atoms
(no UF, no Lean dispatch).  Structurally the mirror of the
`is_sorted` corpus benchmark, with the flag roles swapped so that
flag == 1 marks the *found-a-consecutive-pair* (∃) side and flag ==
0 the *no-pair-yet* (∀) side.  The ∀ branch of the invariant carries
the `or k == n - 1` escape hatch (as in is_sorted) so `i` may
overshoot to n at loop exit without demanding an out-of-bounds
comparison.

Algorithm synthesized:
    flag := 0; i := 0;
    while (i < n - 1):
        if (A[i] + 1 == A[i+1]): flag := 1; i := i + 1;
        else:                    i := i + 1;
    result := flag;
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n >= 0), "
        "return 1 if there is at least one index k with "
        "0 <= k < n-1 such that A[k] + 1 == A[k+1] (a consecutive "
        "pair), otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n >= 0",
    # result == 1 iff a consecutive pair exists.
    post     = (
        "((result == 1) and "
        " Exists(lambda k: 0 <= k and k < n - 1 and A[k] + 1 == A[k + 1])) or "
        "((result == 0) and "
        " ForAll(lambda k: Implies(0 <= k and k < n - 1, A[k] + 1 != A[k + 1])))"
    ),

    atoms = {
        # Init: flag := 0 (nothing found), i := 0.
        "s@B0": [{"flag": "0", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # flag == 1 : a consecutive pair has been found (permanent,
            #             witnessed over the full range).
            # flag == 0 : no consecutive pair in the scanned prefix
            #             [0, i); the `or k == n - 1` escape lets i
            #             overshoot to n at exit without an OOB check.
            ("((flag == 1) and "
             " Exists(lambda k: 0 <= k and k < n - 1 and A[k] + 1 == A[k + 1])) or "
             "((flag == 0) and "
             " ForAll(lambda k: Implies(0 <= k and k < i, "
             "A[k] + 1 != A[k + 1] or k == n - 1)))"),
        ],
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] + 1 == A[i+1] → consecutive pair, flag := 1.
        "g@B1.0": ["A[i] + 1 == A[i + 1]"],
        "s@B1.0": [{"flag": "1", "i": "i + 1"}],
        # Branch 1: A[i] + 1 != A[i+1] → keep scanning, flag unchanged.
        "g@B1.1": ["A[i] + 1 != A[i + 1]"],
        "s@B1.1": [{"i": "i + 1"}],

        # Final: result := flag.
        "s@B2": [{"result": "flag"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_15/lean/SynthLean/Y2Corpus/verina_basic_15",
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
