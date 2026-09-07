"""verina_basic_69 (LinearSearch / LinearSearch2) — VERINA-basic port.

Given an integer array `a` that is GUARANTEED to contain the target
`e` at least once, return the index of the FIRST occurrence of `e`.
Because the element is guaranteed present, there is no sentinel /
"not found" case: the result is always a valid in-bounds index.

VERINA spec (from datasets/verina/verina_basic_69/task.lean,
between the @start/@end markers; source of truth):
    signature : LinearSearch (a : Array Int) (e : Int) -> Nat
    precond   : ∃ i, i < a.size ∧ a[i]! = e
                (the array contains e at least once)
    code      : linearSearchAux a e 0, where
                  linearSearchAux a e n :=
                    if n < a.size then
                      (if a[n]! = e then n
                       else linearSearchAux a e (n+1))
                    else 0
                — linear scan from index 0, return the first index
                  whose element equals e.
    postcond  :
        (result < a.size) ∧
        (a[result]! = e) ∧
        (∀ k : Nat, k < result → a[k]! ≠ e)

Port / fidelity mapping
-----------------------
    A : int[]  = a          (element a[i] ↦ A[i]).
    n : int    = a.size     (VERINA `a.size` is a Nat; passed as an
                             int input with the implicit n ≥ 0 stated
                             in `pre`).
    e : int    = e          (already Int).
    res : int  = result     (VERINA `result` is a Nat; we carry the
                             implicit result ≥ 0 as `0 <= res` in the
                             postcondition — the loop counter is
                             non-negative by construction).

    Pre  : n >= 0
         ∧ Exists(j: 0 <= j < n ∧ A[j] == e)
           — the standard int-encoding of VERINA's
             `∃ i, i < a.size ∧ a[i]! = e`.  `n >= 0` is the implicit
             Nat-size fact; the existential carries VERINA's
             "e occurs somewhere" precondition (the Nat index i
             carries an implicit i ≥ 0, written explicitly as 0 <= j).

    Post : (0 <= res) ∧ (res < n) ∧ (A[res] == e)
         ∧ ForAll(k: 0 <= k < res ⇒ A[k] != e)

SPEC-FIDELITY NOTE
------------------
Faithful.  Our post is a one-for-one transcription of VERINA's
postcond.  `result < a.size` ↦ `res < n`; `a[result]! = e` ↦
`A[res] == e`; `∀ k : Nat, k < result → a[k]! ≠ e` ↦
`ForAll(k: 0 <= k < res ⇒ A[k] != e)` — the leading `0 <= res` and
`0 <= k` make the Nat non-negativity of `result` and the universal's
index explicit (no-ops for the never-reached negative values).  The
precond `∃ i, i < a.size ∧ a[i]! = e` transcribes to
`Exists(j: 0 <= j < n ∧ A[j] == e)`.  So our (pre, post) is faithful
to VERINA's.  This existence precondition is LOAD-BEARING at loop
exit: it is what rules out the "scan ran off the end" state
(res == n) and forces res < n ∧ A[res] == e.

ALGORITHM the synthesizer picks
-------------------------------
A single left-to-right scan; the loop counter IS the returned index.
Because indices are visited in increasing order and the loop stops
at the first hit, the returned index is automatically the FIRST
occurrence.

    res := 0;
    while (res < n and A[res] != e):   # skip the non-e prefix
        res := res + 1;
    # loop exit: (res >= n ∨ A[res] == e), and Pre forces res < n

Loop invariant (tau@L0):
    0 <= res <= n  ∧  n >= 0
  ∧ ForAll(k: 0 <= k < res ⇒ A[k] != e)   (prefix has no e)
At loop exit the guard gives (res >= n) ∨ (A[res] == e).  The
precondition Exists(j: 0 <= j < n ∧ A[j] == e) is threaded into the
exit obligation (framework's Fpre-in-post-bundle): if res >= n then
the prefix invariant covers all of [0, n), contradicting the
existence of a j < n with A[j] == e — hence res < n, and the guard
gives A[res] == e.  Combined with the prefix invariant (∀k<res.
A[k] != e) this discharges the first-occurrence postcondition.

TRUST SURFACE: none beyond Z3.  No uninterpreted function, no axioms,
no Lean dispatch — the invariant and the existence precondition are
expressible with quantified atoms, so Z3 discharges every obligation
(init / inductive / termination / post).  Same family as corpus
`find_first_pos` (first-witness scan) and `verina_basic_37` /
`verina_basic_62` (linear-search first-occurrence), the difference
being verina_69's guaranteed-present precondition (no -1 sentinel).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of size n (n >= 0) and an integer "
        "e that is guaranteed to occur in A at least once, return "
        "the index of the first occurrence of e in A[0..n)."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("e", "int", "input")],
    outputs  = [Var("res", "int", "output")],

    pre = (
        "n >= 0 and "
        "Exists(lambda j: 0 <= j and j < n and A[j] == e)"
    ),
    post = (
        "(0 <= res) and (res < n) and (A[res] == e) and "
        "ForAll(lambda k: Implies(0 <= k and k < res, A[k] != e))"
    ),

    atoms = {
        # Init: start the scan at index 0.
        "s@B0": [{"res": "0"}],

        "tau@L0": [
            "0 <= res",
            "res <= n",
            "n >= 0",
            # Prefix [0, res) contains no occurrence of e.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < res, A[k] != e))"),
        ],
        # Continue while in bounds AND current element is not e.
        "g@L0":   ["(res < n) and (A[res] != e)"],
        "phi@L0": ["n - res"],

        # Loop body: advance the scan.
        "s@B1": [{"res": "res + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/verina_basic_69_LinearSearch2"),
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
