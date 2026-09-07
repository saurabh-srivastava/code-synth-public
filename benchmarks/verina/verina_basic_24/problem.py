"""verina_basic_24 (firstEvenOddDifference) — VERINA-basic port.

Given an integer array containing at least one even and one odd
element, return (first even element) − (first odd element).

VERINA spec (from datasets/verina/verina_basic_24/task.lean,
between the @start/@end markers; source of truth):
    signature : firstEvenOddDifference (a : Array Int) -> Int
    isEven x  := x % 2 == 0        isOdd x := x % 2 != 0
    precond   : a.size > 1
              ∧ (∃ x ∈ a, isEven x)
              ∧ (∃ x ∈ a, isOdd  x)
    code      : sequential scan tracking the first-even and first-odd
                index; returns a[firstEven] − a[firstOdd].
    postcond  : ∃ i j, i < a.size ∧ j < a.size
                     ∧ isEven (a[i]!) ∧ isOdd (a[j]!)
                     ∧ result = a[i]! − a[j]!
                     ∧ (∀ k, k < i → isOdd  (a[k]!))
                     ∧ (∀ k, k < j → isEven (a[k]!))

Port / fidelity mapping
-----------------------
    A : int[]   = a          (element a[i] ↦ A[i])
    n : int     = a.size     (VERINA `a.size` is a Nat; we pass it as an
                              int input; `n > 1` from the precond subsumes
                              the implicit n ≥ 0).
    result : int = the returned Int.
    fe, fo : int (locals) = the first-even index i and first-odd index j
                            — the EXISTENTIAL WITNESSES of VERINA's post,
                            here exposed as concrete program variables so
                            the post is a quantifier-free CHECK (Z3 does
                            not have to guess i, j).

    Pre  : n > 1
         ∧ Exists(t: 0<=t<n ∧ A[t]%2==0)     (∃ x ∈ a, isEven x)
         ∧ Exists(t: 0<=t<n ∧ A[t]%2!=0)     (∃ x ∈ a, isOdd  x)

    Post : 0<=fe<n ∧ 0<=fo<n
         ∧ A[fe]%2==0 ∧ A[fo]%2!=0
         ∧ result == A[fe] - A[fo]
         ∧ ForAll(k: 0<=k<fe ⇒ A[k]%2!=0)    (all before fe are odd)
         ∧ ForAll(k: 0<=k<fo ⇒ A[k]%2==0)    (all before fo are even)

SPEC-FIDELITY NOTE
------------------
Our post is VERINA's post with the two existential witnesses i, j
instantiated by the concrete program variables fe, fo.  It is a
STRENGTHENING: our post ⇒ VERINA's post (instantiate i:=fe, j:=fo),
so any code we verify satisfies VERINA's postcondition.  `isEven x`
(x % 2 == 0) and `isOdd x` (x % 2 != 0) transcribe directly; Lean's
`Int.emod` and Z3's `mod` both return a non-negative remainder for
the positive divisor 2, so `x % 2 ∈ {0,1}` under both semantics and
the even/odd tests agree.  The bounded-index universals
`(∀ k, k < i → …)` are written `0 <= k and k < fe` (the k ≥ 0 lower
bound is implicit in VERINA's Nat index k and is a no-op for k < 0).

ALGORITHM the synthesizer picks
-------------------------------
Because A[0] is itself either even or odd, ONE of {fe, fo} is always
index 0, and the other is the first index whose parity DIFFERS from
A[0].  So a single scan suffices:

    d := 0;
    while (d < n and A[d]%2 == A[0]%2):   # skip the A[0]-parity prefix
        d := d + 1;
    if A[0]%2 == 0:  fe, fo, result := 0, d, A[0] - A[d]   # A[0] even
    else:            fe, fo, result := d, 0, A[d] - A[0]   # A[0] odd

Loop invariant (tau@L0):
    0 <= d <= n
  ∧ ForAll(k: 0<=k<d ⇒ A[k]%2 == A[0]%2)        (prefix is all A[0]-parity)
  ∧ Exists(k: d<=k<n ∧ A[k]%2 != A[0]%2)         (an opposite-parity elt remains)
The Exists conjunct is established at loop entry from the precond's two
existentials (case-split on A[0]%2 ∈ {0,1}) and preserved locally (we
only advance past A[0]-parity elements, so the witness is never d), and
at loop exit it rules out d == n — giving d < n ∧ A[d] opposite-parity.

TRUST SURFACE: none beyond Z3.  No uninterpreted function, no axioms,
no Lean dispatch — the invariant is expressible with quantified tau
atoms, so Z3 discharges every obligation (init / inductive / coverage /
termination / post).  Same family as corpus `find_first_pos`
(first-witness scan) + `array_max_val` (maintained Exists invariant).
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of size n > 1 that contains at least "
        "one even and one odd element, return (first even element) minus "
        "(first odd element)."
    ),

    template = SB() >> Loop(SB()) >> SB(n=2),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("d",  "int", "local"),
                Var("fe", "int", "local"),
                Var("fo", "int", "local")],

    pre = (
        "n > 1 and "
        "Exists(lambda t: 0 <= t and t < n and A[t] % 2 == 0) and "
        "Exists(lambda t: 0 <= t and t < n and A[t] % 2 != 0)"
    ),
    post = (
        "(0 <= fe) and (fe < n) and (0 <= fo) and (fo < n) and "
        "(A[fe] % 2 == 0) and (A[fo] % 2 != 0) and "
        "(result == A[fe] - A[fo]) and "
        "ForAll(lambda k: Implies(0 <= k and k < fe, A[k] % 2 != 0)) and "
        "ForAll(lambda k: Implies(0 <= k and k < fo, A[k] % 2 == 0))"
    ),

    atoms = {
        # Init: start the scan at index 0.
        "s@B0": [{"d": "0"}],

        "tau@L0": [
            "0 <= d",
            "d <= n",
            "n > 1",
            # Prefix [0, d) is entirely of A[0]'s parity.
            ("ForAll(lambda k: Implies("
             "0 <= k and k < d, A[k] % 2 == A[0] % 2))"),
            # An opposite-parity element still remains in [d, n).
            ("Exists(lambda k: d <= k and k < n and "
             "A[k] % 2 != A[0] % 2)"),
        ],
        # Continue while still in bounds AND same parity as A[0].
        "g@L0":   ["(d < n) and (A[d] % 2 == A[0] % 2)"],
        "phi@L0": ["n - d"],

        # Loop body: advance the scan.
        "s@B1": [{"d": "d + 1"}],

        # Final SB(n=2): decide which of {0, d} is the first-even /
        # first-odd index based on A[0]'s parity, then compute result.
        # Branch 0: A[0] even → fe = 0, fo = d.
        "g@B2.0": ["A[0] % 2 == 0"],
        "s@B2.0": [{"fe": "0", "fo": "d", "result": "A[0] - A[d]"}],
        # Branch 1: A[0] odd → fo = 0, fe = d.
        "g@B2.1": ["A[0] % 2 != 0"],
        "s@B2.1": [{"fe": "d", "fo": "0", "result": "A[d] - A[0]"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = (
        "lean/SynthLean/Y2Corpus/verina_basic_24_firstEvenOddDifference"),
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
