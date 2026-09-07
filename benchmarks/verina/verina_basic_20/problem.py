"""verina_basic_20_uniqueProduct — VERINA-basic port (uniqueProduct).

Ported from VERINA task `verina_basic_20` (uniqueProduct; upstream
dafny-synthesis task_id_573).  Compute the product of all DISTINCT
integers in an array (each unique value multiplied in exactly once;
the empty array yields the product 1).

VERINA signature (source of truth):
    uniqueProduct(arr : Array Int) -> Int
VERINA precondition: True.
VERINA postcondition (source of truth, from task.lean):
    result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
    (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0
  i.e.  result = arr.toList.eraseDups.foldl (· * ·) 1
        (the product over the DISTINCT elements of arr, keeping the
        first occurrence of each value; order is irrelevant since `*`
        is commutative — see the task description's -----Note-----).

VERINA reference code (source of truth, from task.lean):
    loop (i) (seen) (product):
      if i < arr.size:
        x := arr[i]
        if seen.contains x then loop (i+1) seen product
        else                    loop (i+1) (seen.insert x) (product * x)
      else product
    loop 0 ∅ 1
  i.e. walk left-to-right; multiply arr[i] into the running product
  IFF arr[i] has NOT been seen earlier (first occurrence), else skip.

Framework encoding
------------------
    Pre  : n >= 0                        (n = arr.size; a Nat, so n ≥ 0)
    Post : p == uprod(A, n)

Two uninterpreted functions abstract the VERINA fold:
  * `uprod : (Int → Int) → Int → Int`  — product of the distinct
    elements of the prefix A[0..k).  This IS `eraseDups.foldl (·*·) 1`
    read as a forward prefix recurrence.
  * `seen  : (Int → Int) → Int → Int`  — the prefix-membership
    predicate:  seen(A, k) is nonzero iff A[k] already occurred among
    A[0..k) (i.e. `seen.contains x` at loop step k in the VERINA code).
    Left uninterpreted (defined only through the recurrence that uses
    it), exactly as `count`/`count_less` are in the corpus count-fold
    benchmarks — the recurrence IS the definition of the fold.

Axioms (base + the two per-branch step recurrences):
  - uprod(A, 0)                             = 1                (empty prefix ⇒ product 1)
  - seen(A,k) == 0 ⇒ uprod(A, k+1)          = uprod(A, k) * A[k]   (first occurrence ⇒ multiply)
  - seen(A,k) != 0 ⇒ uprod(A, k+1)          = uprod(A, k)          (repeat ⇒ skip)

Same case-split fold shape as the corpus benchmarks `count_zeros`
and `count_less_than`; the only structural differences are (a) the
branch predicate is a UF `seen(A,i)` (not a concrete comparison on
A[i]) and (b) the "do" branch multiplies (`p := p * A[i]`) instead
of incrementing.  The branch guards `seen(A,i)==0` / `seen(A,i)!=0`
partition all cases (coverage is the tautology x==0 ∨ x!=0).

SPEC-FIDELITY NOTE
------------------
Our `uprod` axioms ARE the definitional unfolding of VERINA's
`eraseDups.foldl (·*·) 1` over the prefix A[0..k):
  * `uprod(A, 0) = 1` is the fold's initial accumulator on the empty
    (dedup'd) prefix.
  * the two step axioms are exactly the VERINA loop step: multiply
    A[k] iff it is a first occurrence (`¬seen.contains`), else skip.
    `seen(A,k)` stands for the VERINA HashSet's `.contains arr[k]`
    at step k, i.e. the prefix-membership predicate A[k] ∈ A[0..k).
Because `*` is commutative (task -----Note-----), multiplying the
first occurrences left-to-right equals the product over the distinct
value SET; hence, by induction on the prefix length, uprod(A, n) =
arr.toList.eraseDups.foldl (·*·) 1 when n = arr.size.  Therefore our
post `p == uprod(A, n)` is equivalent to VERINA's `result = foldl(...)`
(the `a-b=0 ∧ b-a=0` phrasing in task.lean is just `a = b`).

TRUST SURFACE: the three `uprod`/`seen` axioms above (base + two
per-branch step recurrences).  Everything else about the synthesized
loop (per-branch inductiveness, coverage, termination, exit bridge)
is discharged by Lean `.solved.lean` companions from concrete UF
semantics.  `seen` being uninterpreted is the standard count-fold
abstraction (cf. `count` in count_zeros) — the recurrence is its
definition.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "return the product of the DISTINCT values among A[0], "
        "A[1], ..., A[n-1] (empty prefix ⇒ 1)."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("p", "int", "output")],
    locals   = [Var("i", "int", "local")],

    uninterpreted = [
        ("uprod", ["int[]", "int"], "int"),
        ("seen",  ["int[]", "int"], "int"),
    ],
    axioms = [
        # Base: empty (dedup'd) prefix ⇒ product 1.
        "uprod(A, 0) == 1",
        # First occurrence (seen==0) ⇒ multiply A[k] in.
        ("ForAll(lambda k: Implies(k >= 0 and seen(A, k) == 0, "
         "uprod(A, k + 1) == uprod(A, k) * A[k]))"),
        # Repeat (seen!=0) ⇒ product unchanged.
        ("ForAll(lambda k: Implies(k >= 0 and seen(A, k) != 0, "
         "uprod(A, k + 1) == uprod(A, k)))"),
    ],

    pre  = "n >= 0",
    post = "p == uprod(A, n)",

    atoms = {
        "s@B0": [{"p": "1", "i": "0"}],

        "tau@L0": [
            "p == uprod(A, i)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: seen(A,i) == 0 (first occurrence) → p := p*A[i], i := i+1.
        "g@B1.0": ["seen(A, i) == 0"],
        "s@B1.0": [{"p": "p * A[i]", "i": "i + 1"}],
        # Branch 1: seen(A,i) != 0 (repeat) → i := i + 1.
        "g@B1.1": ["seen(A, i) != 0"],
        "s@B1.1": [{"i": "i + 1"}],

        "s@B2": [{}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 7,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_20/lean/SynthLean/Y2Corpus/verina_basic_20",
    wedge_threshold = 200,
    solver_timeout_ms = 1_800_000,   # 30 min budget for axiom-heavy
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
