"""verina_basic_19 (isSorted) — VERINA-basic port.

Check whether an integer array is sorted in non-decreasing order.
Returns 1 (true) if every element is ≤ the one that follows it,
0 (false) otherwise.

VERINA spec (from datasets/verina/verina_basic_19/task.lean,
between the @start/@end markers; source of truth):
    signature : isSorted (a : Array Int) -> Bool
    precond   : True
    code      : if a.size ≤ 1 then true
                else a.mapIdx (fun i x =>
                       if h : i + 1 < a.size then decide (x ≤ a[i+1])
                       else true) |>.all id
    postcond  : (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result

Port / fidelity mapping
-----------------------
    Pre  : n >= 0            (n = a.size; a Nat, hence n ≥ 0.  VERINA
                              precond is `True` — the n ≥ 0 fact is the
                              only content of the Array-size Nat and is
                              needed by the loop invariant.)
    Post : ((result == 1) and ∀k. 0 ≤ k < n-1 ⇒ A[k] ≤ A[k+1]) or
           ((result == 0) and ∃k. 0 ≤ k < n-1 ∧ A[k] > A[k+1])

    VERINA output var `result : Bool` -> our output var `result : int`
    with the Bool→{0,1} convention (1 = true, 0 = false).

SPEC-FIDELITY NOTE
------------------
VERINA's postcond is the biconditional `SORTED ↔ result`, where
`SORTED ≡ ∀ i < a.size - 1, a[i] ≤ a[i+1]`.  Our post writes the
SAME biconditional in explicit case-split form over a {0,1}-valued
`result`:
  * `result == 1  ⇒  SORTED`             (the `(result==1) ∧ SORTED` disjunct)
  * `result == 0  ⇒  ¬SORTED`            (the `(result==0) ∧ ∃-inversion` disjunct)
`¬SORTED` over integers is exactly "∃ an adjacent pair A[k] > A[k+1]"
(the negation of "∀ adjacent pairs are non-decreasing"), so the
Exists disjunct is the literal De Morgan dual of the ForAll disjunct.
Given `result ∈ {0,1}`, the disjunction `(1 ∧ SORTED) ∨ (0 ∧ ¬SORTED)`
is logically equivalent to `SORTED ↔ (result == 1)` — a faithful
transcription of VERINA's `↔`.

Nat-subtraction corner cases match VERINA:
  * n = 0 (empty array): VERINA's `a.size - 1 = 0` (Nat truncation),
    so `i < 0` is unsatisfiable → SORTED vacuously true → result true.
    Our `n - 1 = -1`, so `0 ≤ k < -1` is unsatisfiable → ForAll
    vacuously true, Exists false → result 1.  Match.
  * n = 1: VERINA `a.size - 1 = 0` → vacuous → true.  Ours `n-1 = 0`,
    `0 ≤ k < 0` unsatisfiable → result 1.  Match.

Same shape as corpus `is_sorted` / `all_positive` (single-pass
flag-fold with early-set flag + branched body).  PURE Z3: no
uninterpreted function, no axioms, no Lean dispatch — the invariant
`flag == 1 ⇔ prefix [0,i) has no adjacent inversion` is expressible
with a quantified tau atom, so Z3 discharges the whole obligation.

TRUST SURFACE: none beyond Z3.  No axioms; the result rests only on
the SMT solver's discharge of the loop invariant / coverage /
termination obligations.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "return 1 if A[0] ≤ A[1] ≤ ... ≤ A[n-1] (non-decreasing), "
        "otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n >= 0",
    # VERINA postcond `SORTED ↔ result`, in explicit {0,1} case-split form.
    post     = (
        "((result == 1) and "
        " ForAll(lambda k: Implies("
        "0 <= k and k < n - 1, A[k] <= A[k + 1]))) or "
        "((result == 0) and "
        " Exists(lambda k: 0 <= k and k < n - 1 and A[k] > A[k + 1]))"
    ),

    atoms = {
        "s@B0": [{"flag": "1", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # flag is 1 iff prefix [0, i) has no adjacent inversion.
            ("((flag == 1) and "
             " ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] <= A[k + 1] or k == n - 1))) or "
             "((flag == 0) and "
             " Exists(lambda k: 0 <= k and k < n - 1 and A[k] > A[k + 1]))"),
        ],
        "g@L0":   ["i < n - 1"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] <= A[i+1] → no flip; advance.
        "g@B1.0": ["A[i] <= A[i + 1]"],
        "s@B1.0": [{"i": "i + 1"}],
        # Branch 1: A[i] > A[i+1] → flag := 0; advance.
        "g@B1.1": ["A[i] > A[i + 1]"],
        "s@B1.1": [{"flag": "0", "i": "i + 1"}],

        "s@B2": [{"result": "flag"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_19/lean/SynthLean/Y2Corpus/verina_basic_19",
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
