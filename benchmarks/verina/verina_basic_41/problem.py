"""verina_basic_41 (hasOnlyOneDistinctElement) — VERINA-basic port.

Determine whether an integer array contains only one distinct element,
i.e. every element equals the first.  Returns 1 (true) if all elements
are identical, 0 (false) if there are at least two distinct values.

VERINA spec (from datasets/verina/verina_basic_41/task.lean, between
the @start/@end markers; source of truth):
    signature : hasOnlyOneDistinctElement (a : Array Int) -> Bool
    precond   : a.size > 0
    code      : if a.size = 0 then true
                else let firstElement := a[0]!
                     let rec loop (i) := if i < a.size then
                       (if a[i]! = firstElement then loop (i+1) else false)
                       else true
                     loop 1
    postcond  : let l := a.toList
                (result → List.Pairwise (· = ·) l) ∧
                (¬ result → (l.any (fun x => x ≠ l[0]!)))

Port / fidelity mapping
-----------------------
    Pre  : n > 0             (n = a.size; VERINA precond `a.size > 0`.)
    Post : ((result == 1) and ∀k. 0 ≤ k < n ⇒ A[k] == A[0]) or
           ((result == 0) and ∃k. 0 ≤ k < n ∧ A[k] != A[0])

    VERINA output var `result : Bool` -> our output var `result : int`
    with the Bool→{0,1} convention (1 = true, 0 = false).  VERINA's
    `firstElement = a[0]! = l[0]!` -> our `A[0]`.

SPEC-FIDELITY NOTE
------------------
VERINA's postcond is the conjunction of two implications:
  (result → Pairwise(·=·) l)  ∧  (¬result → l.any(x ≠ l[0])).
`List.Pairwise (· = ·) l` means every pair of elements is equal; for a
NONEMPTY list (guaranteed by precond a.size > 0) this is EXACTLY
"every element equals l[0]" (l[0]=l[k] ∀k, and any pair l[i]=l[0]=l[j]).
`l.any (fun x => x ≠ l[0]!)` is exactly "∃ an element ≠ l[0]", the
literal De Morgan dual of the ForAll.

Our post writes the SAME two implications in explicit {0,1} case-split
disjunctive form:
  * `result == 1  ⇒  ALLEQ`      (the `(result==1) ∧ ForAll` disjunct)
  * `result == 0  ⇒  ∃DIFF`      (the `(result==0) ∧ Exists` disjunct)
Given `result ∈ {0,1}`, `(1 ∧ ALLEQ) ∨ (0 ∧ ∃DIFF)` is logically
equivalent to `(result → ALLEQ) ∧ (¬result → ∃DIFF)` — a faithful
transcription of VERINA's conjunction (equivalently `ALLEQ ↔ result`,
since ∃DIFF = ¬ALLEQ).

Same shape as corpus `all_positive` / `is_sorted` (single-pass
flag-fold with early-set flag + branched body).  PURE Z3: no
uninterpreted function, no axioms, no Lean dispatch — the invariant
`flag == 1 ⇔ prefix [0,i) all equal A[0]` is expressible with a
quantified tau atom, so Z3 discharges the whole obligation.

TRUST SURFACE: none beyond Z3.  No axioms; the result rests only on
the SMT solver's discharge of the loop invariant / coverage /
termination obligations.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n > 0), "
        "return 1 if every element A[0], A[1], ..., A[n-1] equals "
        "A[0] (the array has only one distinct value), otherwise "
        "return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n > 0",
    # VERINA postcond, in explicit {0,1} case-split form.  ALLEQ ≡
    # "every element equals A[0]"; ∃DIFF ≡ "some element differs".
    post     = (
        "((result == 1) and "
        " ForAll(lambda k: Implies(0 <= k and k < n, A[k] == A[0]))) or "
        "((result == 0) and "
        " Exists(lambda k: 0 <= k and k < n and A[k] != A[0]))"
    ),

    atoms = {
        # Init: flag := 1, i := 0.  (A[0]==A[0] is trivially true, so
        # scanning from 0 is equivalent to VERINA's loop-from-1.)
        "s@B0": [{"flag": "1", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # flag is 1 iff prefix [0, i) all equal A[0].
            ("((flag == 1) and "
             " ForAll(lambda k: Implies(0 <= k and k < i, A[k] == A[0]))) or "
             "((flag == 0) and "
             " Exists(lambda k: 0 <= k and k < i and A[k] != A[0]))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] == A[0] → flag stays, advance i.
        "g@B1.0": ["A[i] == A[0]"],
        "s@B1.0": [{"i": "i + 1"}],
        # Branch 1: A[i] != A[0] → flag := 0, advance i.
        "g@B1.1": ["A[i] != A[0]"],
        "s@B1.1": [{"flag": "0", "i": "i + 1"}],

        # Final: result := flag.
        "s@B2": [{"result": "flag"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_41/lean/SynthLean/Y2Corpus/verina_basic_41",
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
