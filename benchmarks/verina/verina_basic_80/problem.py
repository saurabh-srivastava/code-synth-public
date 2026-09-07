"""verina_basic_80_only_once — VERINA-basic port (only_once).

Ported from VERINA task `verina_basic_80` (only_once; upstream Clover
`only_once`).  Determine whether a given `key` appears EXACTLY ONCE in
an integer array.  Returns a Bool.

VERINA spec (from datasets/verina/verina_basic_80/task.lean, between
the @start/@end markers; source of truth):
    signature : only_once (a : Array Int) (key : Int) -> Bool
    precond   : True                       (no preconditions)
    code      : only_once_loop a key 0 0     -- a tail-recursive scan
                that counts occurrences of `key` and returns
                `keyCount == 1` at the end.
    postcond  : let count_occurrences a key :=
                    a.foldl (fun cnt x => if x = key then cnt+1 else cnt) 0
                ((count_occurrences a key = 1) → result) ∧
                ((count_occurrences a key ≠ 1) → ¬ result)
              i.e. result ↔ (count_occurrences a key = 1).

Port / fidelity mapping
-----------------------
    Pre  : n >= 0            (n = a.size; a Nat, so n ≥ 0.  VERINA's
                              precond is `True`; n ≥ 0 is the implied
                              Nat constraint on the array size.)
    Post : ((count_occ(A, key, n) == 1) and (result == 1)) or
           ((count_occ(A, key, n) != 1) and (result == 0))

    VERINA output var `result : Bool` -> our output var `result : int`
    with the Bool→{0,1} convention (1 = true, 0 = false).
    VERINA's `key : Int` -> our input `key`.

`count_occ : (Int → Int) → Int → Int → Int` is uninterpreted and
re-axiomatizes VERINA's `count_occurrences` left fold as a forward
prefix recurrence over the array prefix A[0..k):
  - count_occ(A, key, 0)                        = 0            (empty prefix)
  - A[k] == key ⇒ count_occ(A, key, k+1) = count_occ(A, key, k) + 1
  - A[k] != key ⇒ count_occ(A, key, k+1) = count_occ(A, key, k)

The synthesized program counts occurrences of `key` into a local `c`
via a single forward pass (SB(n=2) body: hit-branch increments c,
miss-branch skips), then the final SB sets `result := (c == 1) ? 1 : 0`
— exactly VERINA's `only_once_loop ...; keyCount == 1`.

Same UF + case-split-recurrence shape as corpus `count_equal`
(runtime-parameter target) and the shipped verina port
`verina_basic_57_count_less_than`; this is `count_equal` with the
final `result := (c == 1)` boolean comparison bolted on (like
`all_positive` / `verina_basic_41`'s flag→result move, but the
predicate is "count == 1", which is NOT prefix-monotone and hence
requires the count UF rather than a monotone flag).

SPEC-FIDELITY NOTE
------------------
Our `count_occ` axioms ARE the definitional unfolding of VERINA's
`count_occurrences a key = a.foldl (fun cnt x => if x = key then
cnt+1 else cnt) 0` over the prefix A[0..k):
  * `count_occ(A, key, 0) = 0` is the fold's initial accumulator on
    the empty prefix.
  * the two step axioms are exactly the fold's step function
    `fun cnt x => if x = key then cnt+1 else cnt`, specialised on
    whether A[k] = key.
By induction on prefix length, `count_occ(A, key, n) =
count_occurrences a key` when `n = a.size`.  Our post
`(count_occ(A,key,n)==1 ∧ result==1) ∨ (count_occ(A,key,n)!=1 ∧
result==0)` is, given `result ∈ {0,1}`, logically equivalent to
VERINA's `((count=1)→result) ∧ ((count≠1)→¬result)` (equivalently
`result ↔ count=1`).  FAITHFUL.

TRUST SURFACE: the three `count_occ` axioms above (base + the two
per-branch step recurrences).  Everything else about the synthesized
loop (per-branch inductiveness, coverage, termination) and the final
`result := (c==1)?1:0` comparison is discharged by the framework /
Lean `.solved.lean` companions.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A, a length n (with n ≥ 0), and an "
        "integer key, return 1 if `key` appears EXACTLY ONCE among "
        "A[0], A[1], ..., A[n-1], otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input"),
                Var("key", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("c", "int", "local"),
                Var("i", "int", "local")],

    uninterpreted = [("count_occ", ["int[]", "int", "int"], "int")],
    axioms = [
        "count_occ(A, key, 0) == 0",
        ("ForAll(lambda k: Implies(k >= 0 and A[k] == key, "
         "count_occ(A, key, k + 1) == count_occ(A, key, k) + 1))"),
        ("ForAll(lambda k: Implies(k >= 0 and A[k] != key, "
         "count_occ(A, key, k + 1) == count_occ(A, key, k)))"),
    ],

    pre  = "n >= 0",
    # result is 1 iff `key` occurs exactly once in A[0..n).
    post = (
        "((count_occ(A, key, n) == 1) and (result == 1)) or "
        "((count_occ(A, key, n) != 1) and (result == 0))"
    ),

    atoms = {
        # Init: c := 0, i := 0.
        "s@B0": [{"c": "0", "i": "0"}],

        "tau@L0": [
            "c == count_occ(A, key, i)",
            "0 <= i",
            "i <= n",
            "n >= 0",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] == key → c := c + 1, i := i + 1.
        "g@B1.0": ["A[i] == key"],
        "s@B1.0": [{"c": "c + 1", "i": "i + 1"}],
        # Branch 1: A[i] != key → i := i + 1.
        "g@B1.1": ["A[i] != key"],
        "s@B1.1": [{"i": "i + 1"}],

        # Final: result := (c == 1) ? 1 : 0.
        "s@B2": [{"result": "1 if c == 1 else 0"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_80/lean/SynthLean/Y2Corpus/verina_basic_80",
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
