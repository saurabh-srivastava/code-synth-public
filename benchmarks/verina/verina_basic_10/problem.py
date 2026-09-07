"""verina_basic_10_isGreater — VERINA-basic port (isGreater).

Ported from VERINA task `verina_basic_10` (isGreater; upstream
dafny-synthesis task_id_433).  Determine whether an integer is
strictly greater than EVERY element of an array.

VERINA signature (source of truth):
    isGreater(n : Int, a : Array Int) -> Bool
VERINA precondition (task.lean, between @start/@end precond):
    a.size > 0
VERINA reference code:
    a.all fun x => n > x
VERINA postcondition (task.lean, between @start/@end postcond):
    (∀ i, (hi : i < a.size) → n > a[i]) ↔ result

Framework encoding
------------------
    Pre  : n > 0                          (n = array length; VERINA's a.size > 0)
    Post : ((result == 1) ∧ ∀k. 0 ≤ k < n ⇒ t > A[k])
         ∨ ((result == 0) ∧ ∃k. 0 ≤ k < n ∧ t <= A[k])

NAMING MAP (VERINA -> ours):
    VERINA `a`      (Array Int)     -> our `A`  (int[])
    VERINA `a.size` (Nat, > 0)      -> our `n`  (int, with n > 0)
    VERINA `n`      (Int, scalar)   -> our `t`  (int, the threshold)
    VERINA `result` (Bool)          -> our `result` (int, 0/1)

This is a flag-fold "all elements satisfy a predicate" benchmark —
structurally identical to the corpus benchmark `all_positive` (which
checks `A[k] > 0`); here the per-element predicate is `t > A[k]`
(the scalar strictly greater than the element).  Pure Z3 with a
quantified loop invariant; no uninterpreted functions.

SPEC-FIDELITY NOTE
------------------
VERINA's postcond is the biconditional
    (∀ i < a.size, n > a[i])  ↔  result.
Our disjunctive post encodes exactly this biconditional over the
Bool→{0,1} coding of `result`:
  * result == 1  ⇔  ∀k∈[0,n). t > A[k]   (forward + false-branch of iff)
  * result == 0  ⇔  ∃k∈[0,n). t <= A[k]  (the negation, i.e. some
    element is ≥ t, which is exactly ¬(∀k. t > A[k])).
Since result ∈ {0,1} is total, the two disjuncts partition the state
space, so the disjunction is logically the iff.  VERINA's `n > a[i]`
is our `t > A[k]`; VERINA's array-bound `i < a.size` is our
`0 <= k < n`.  Precond `a.size > 0` is our `n > 0`.  TRUST SURFACE:
pure Z3 (no axioms).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n (with n > 0), and an "
        "integer t, return 1 if t is strictly greater than every "
        "element A[0], A[1], ..., A[n-1], otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("t", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n > 0",
    # result is 1 iff t is strictly greater than all elements.
    post     = (
        "((result == 1) and "
        " ForAll(lambda k: Implies(0 <= k and k < n, t > A[k]))) or "
        "((result == 0) and "
        " Exists(lambda k: 0 <= k and k < n and t <= A[k]))"
    ),

    atoms = {
        # Init: flag := 1, i := 0.
        "s@B0": [{"flag": "1", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # flag is 1 iff prefix [0, i) is all-below-t (t > A[k]).
            ("((flag == 1) and "
             " ForAll(lambda k: Implies(0 <= k and k < i, t > A[k]))) or "
             "((flag == 0) and "
             " Exists(lambda k: 0 <= k and k < i and t <= A[k]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: t > A[i] → flag stays, advance i.
        "g@B1.0": ["t > A[i]"],
        "s@B1.0": [{"i": "i + 1"}],
        # Branch 1: t <= A[i] → flag := 0, advance i.
        "g@B1.1": ["t <= A[i]"],
        "s@B1.1": [{"flag": "0", "i": "i + 1"}],

        # Final: result := flag.
        "s@B2": [{"result": "flag"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_10/lean/SynthLean/Y2Corpus/verina_basic_10",
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
    for idx, sol in enumerate(result.solutions):
        print(f"── solution #{idx} (score={sol.score:g}) ──")
        print(sol.code)
        print()
