"""verina_basic_68 (LinearSearch) — VERINA-basic port.

Linear search returning the index of the FIRST occurrence of a
target `e` in an integer array, or the array's SIZE if `e` does
not occur.  Same algorithm family as verina_basic_62 (Find) and
verina_basic_37 (findFirstOccurrence), but the "not found"
sentinel is `a.size` (a Nat) rather than -1 — so the loop index
IS the result and no final SB(n=2) mapping is needed (identical
shape to corpus `find_first_pos`).

VERINA spec (from datasets/verina/verina_basic_68/task.lean,
between the @start/@end markers; source of truth):
    signature : LinearSearch (a : Array Int) (e : Int) -> Nat
    precond   : True
    code      : let rec loop (n) := if n < a.size then
                  (if a[n]! = e then n else loop (n+1)) else n
                loop 0
                — linear scan from index 0, return first hit, and
                  return a.size if the scan runs off the end.
    postcond  :
        result ≤ a.size
        ∧ (result = a.size ∨ a[result]! = e)
        ∧ (∀ i, i < result → a[i]! ≠ e)

Port / fidelity mapping
-----------------------
    A : int[]   = a          (element a[i] ↦ A[i]).
    n : int     = a.size     (VERINA `a.size` is a Nat; passed as an
                              int input with the implicit n ≥ 0 stated
                              in `pre` — VERINA's precond `True` adds
                              nothing beyond this size-nonnegativity).
    e : int     = e          (already Int).
    res : int   = result     (result is a Nat; the loop invariant
                              proves 0 ≤ res ≤ n, so the int-encoded
                              `res` faithfully represents the Nat).

    Pre  : n >= 0
           — the only content of VERINA's `True` precond that our
             int-encoding must carry: an Array's `.size` is a Nat,
             hence ≥ 0.  Nothing else is assumed.

    Post : (res <= n)
         ∧ ((res == n) or (A[res] == e))
         ∧ ForAll(k: 0<=k<res ⇒ A[k] != e)

SPEC-FIDELITY NOTE
------------------
Faithful.  Our post is a one-for-one transcription of VERINA's
postcond.  Clause 1 (`res <= n`) transcribes `result ≤ a.size`.
Clause 2 (`res == n or A[res] == e`) transcribes
`result = a.size ∨ a[result]! = e`; when `res == n` the first
disjunct fires and `A[res]` (out of bounds, VERINA's `a[n]!`) is
never inspected, and when `res < n` the read is in bounds.
Clause 3 (`∀ k < res. A[k] != e`) transcribes the "no earlier
occurrence" universal.  VERINA's `∀ i : Nat, i < result` carries
an implicit i ≥ 0 (Nat index); we add the explicit `0 <= k` lower
bound, a no-op for the never-reached k < 0.  The result being a
Nat is captured by the loop invariant `0 <= res` (see tau@L0).

ALGORITHM the synthesizer picks
-------------------------------
A single left-to-right scan.  Because indices are visited in
increasing order and the loop stops at the first hit, the returned
index is automatically the FIRST occurrence; on running off the
end the index equals n = a.size, i.e. the "not found" sentinel.

    res := 0;
    while (res < n and A[res] != e):   # skip the non-e prefix
        res := res + 1;
    # exit with res == n (absent) or A[res] == e (first hit)

Loop invariant (tau@L0):
    0 <= res <= n  ∧  n >= 0
  ∧ ForAll(k: 0<=k<res ⇒ A[k] != e)   (prefix has no e)
At loop exit the guard gives (res >= n) ∨ (A[res] == e); combined
with res <= n and the prefix invariant this discharges the post:
  - res <= n                                       (clause 1);
  - res >= n ⇒ res == n, else A[res] == e          (clause 2);
  - ∀k<res. A[k] != e                              (clause 3).

TRUST SURFACE: none beyond Z3.  No uninterpreted function, no
axioms, no Lean dispatch — the invariant is expressible with
quantified tau atoms, so Z3 discharges every obligation (init /
inductive / coverage / termination / post).  Same family as corpus
`find_first_pos` (first-witness scan returning n on not-found) and
verina_basic_62 / verina_basic_37.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of size n (n >= 0) and an integer "
        "e, return the index of the first occurrence of e in "
        "A[0..n), or n if e does not occur.  No precondition on the "
        "array contents or ordering."
    ),

    template = SB() >> Loop(SB()),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("e", "int", "input")],
    outputs  = [Var("res", "int", "output")],

    pre = "n >= 0",
    post = (
        "(res <= n) and "
        "((res == n) or (A[res] == e)) and "
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
        "lean/SynthLean/Y2Corpus/verina_basic_68_LinearSearch"),
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
