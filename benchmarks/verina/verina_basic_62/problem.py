"""verina_basic_62 (Find) — VERINA-basic port.

Linear search: return the index of the FIRST occurrence of `key`
in an integer array, or -1 if `key` does not occur.  Same
algorithm family as verina_basic_37 (findFirstOccurrence), but
with NO precondition (VERINA's precond is `True` — the array may
be empty or non-empty, sorted or not).

VERINA spec (from datasets/verina/verina_basic_62/task.lean,
between the @start/@end markers; source of truth):
    signature : Find (a : Array Int) (key : Int) -> Int
    precond   : True
    code      : let rec search (index) := if index < a.size then
                  (if a[index]! = key then Int.ofNat index
                   else search (index+1)) else -1
                search 0
                — linear scan from index 0, return first hit, -1 if
                  the scan runs off the end.
    postcond  :
        (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
        ∧ ((result ≠ -1) →
              (a[(Int.toNat result)]! = key ∧
               ∀ i, i < Int.toNat result → a[i]! ≠ key))
        ∧ ((result = -1) →
              ∀ i, i < a.size → a[i]! ≠ key)

Port / fidelity mapping
-----------------------
    A : int[]   = a          (element a[i] ↦ A[i]).
    n : int     = a.size     (VERINA `a.size` is a Nat; passed as an
                              int input with the implicit n ≥ 0 stated
                              in `pre` — VERINA's precond `True` adds
                              nothing beyond this size-nonnegativity).
    key : int   = key        (already Int).
    res : int   = result     (already Int; sentinel -1 for "not found").

    Pre  : n >= 0
           — the only content of VERINA's `True` precond that our
             int-encoding must carry: an Array's `.size` is a Nat,
             hence ≥ 0.  Nothing else is assumed (no sortedness).

    Post : (res == -1 or (res >= 0 and res < n))
         ∧ (res != -1 ⇒ A[res] == key
                       ∧ ForAll(k: 0<=k<res ⇒ A[k] != key))
         ∧ (res == -1 ⇒ ForAll(k: 0<=k<n ⇒ A[k] != key))

SPEC-FIDELITY NOTE
------------------
Faithful.  Our post is a one-for-one transcription of VERINA's
postcond.  Clause 1 (`res == -1 or (res >= 0 and res < n)`) transcribes
`result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size)` directly.
In clause 2 the guard `res != -1`, combined with clause 1, forces
`res ≥ 0 ∧ res < n`, so `Int.toNat result` collapses to `res` (a
Z3 int) and `a[(Int.toNat result)]! = key` becomes `A[res] == key`;
the `∀ i < Int.toNat result. a[i]! ≠ key` first-occurrence clause
transcribes to `ForAll(k: 0<=k<res ⇒ A[k] != key)`.  Clause 3
(`res == -1 ⇒ ∀ k < n. A[k] != key`) transcribes the absent-everywhere
clause.  VERINA's `∀ i : Nat, i < …` universals carry an implicit
i ≥ 0 (Nat index); we add the explicit `0 <= k` lower bound, a no-op
for the never-reached k < 0.

ALGORITHM the synthesizer picks
-------------------------------
A single left-to-right scan.  Because indices are visited in
increasing order and the loop stops at the first hit, the returned
index is automatically the FIRST occurrence.

    i := 0;
    while (i < n and A[i] != key):   # skip the non-key prefix
        i := i + 1;
    if i >= n:  res := -1            # ran off the end: absent
    else:       res := i            # A[i] == key: first hit

Loop invariant (tau@L0):
    0 <= i <= n  ∧  n >= 0
  ∧ ForAll(k: 0<=k<i ⇒ A[k] != key)   (prefix has no key)
At loop exit the guard gives (i >= n) ∨ (A[i] == key); combined with
i <= n and the prefix invariant this discharges both post branches:
  - i >= n ⇒ i == n ⇒ ∀k<n. A[k] != key      (res = -1 clause);
  - i <  n ⇒ A[i] == key ∧ ∀k<i. A[k] != key  (first-occurrence).

TRUST SURFACE: none beyond Z3.  No uninterpreted function, no axioms,
no Lean dispatch — the invariant is expressible with quantified tau
atoms, so Z3 discharges every obligation (init / inductive / coverage /
termination / post).  Same family as corpus `find_first_pos`
(first-witness scan) and `verina_basic_37` (scan + final SB(n=2) map).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of size n (n >= 0) and an integer "
        "key, return the index of the first occurrence of key in "
        "A[0..n), or -1 if key does not occur.  No precondition on "
        "the array contents or ordering."
    ),

    template = SB() >> Loop(SB()) >> SB(n=2),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("key", "int", "input")],
    outputs  = [Var("res", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre = "n >= 0",
    post = (
        "(res == -1 or (res >= 0 and res < n)) and "
        "Implies(res != -1, "
        "  (A[res] == key) and "
        "  ForAll(lambda k: Implies(0 <= k and k < res, "
        "  A[k] != key))) and "
        "Implies(res == -1, "
        "  ForAll(lambda k: Implies(0 <= k and k < n, "
        "  A[k] != key)))"
    ),

    atoms = {
        # Init: start the scan at index 0.
        "s@B0": [{"i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # Prefix [0, i) contains no occurrence of key.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, A[k] != key))"),
        ],
        # Continue while in bounds AND current element is not key.
        "g@L0":   ["(i < n) and (A[i] != key)"],
        "phi@L0": ["n - i"],

        # Loop body: advance the scan.
        "s@B1": [{"i": "i + 1"}],

        # Final SB(n=2): map scan outcome to the result.
        # Branch 0: ran off the end (i == n) → not found → -1.
        "g@B2.0": ["i >= n"],
        "s@B2.0": [{"res": "-1"}],
        # Branch 1: stopped in bounds (A[i] == key) → first hit i.
        "g@B2.1": ["i < n"],
        "s@B2.1": [{"res": "i"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/verina_basic_62_Find"),
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
