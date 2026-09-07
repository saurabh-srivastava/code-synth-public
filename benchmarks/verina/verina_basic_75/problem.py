"""verina_basic_75 (minArray) — VERINA-basic port.

Find the minimum element of a non-empty integer array and return it.

VERINA spec (from datasets/verina/verina_basic_75/task.lean,
between the @start/@end markers; source of truth):
    signature : minArray (a : Array Int) -> Int
    precond   : a.size > 0
    code      : loop a 1 (a[0]!)          -- start at idx 1, min := a[0]
                where `loop a i cur` recursively takes
                `min(cur, a[i])` scanning i .. a.size-1.
    postcond  : (∀ i : Nat, i < a.size → result <= a[i]!) ∧
                (∃ i : Nat, i < a.size ∧ result = a[i]!)

Port / fidelity mapping
-----------------------
    Pre  : n >= 1            (n = a.size; VERINA's `a.size > 0` is
                              exactly `size >= 1` over the Nat size.)
    Post : (∀k. 0 ≤ k < n ⇒ m <= A[k]) ∧ (∃k. 0 ≤ k < n ∧ m == A[k])

    VERINA output `result : Int` -> our output var `m : int`.
    VERINA `a : Array Int`       -> our `A : int[]` + explicit length
    `n : int` (= a.size), the standard array-scalar port shape.

SPEC-FIDELITY NOTE
------------------
Our post is a literal transcription of VERINA's two conjuncts:
  * lower-bound      : `∀ i < a.size, result <= a[i]!`
                       -> `ForAll k. 0 ≤ k < n ⇒ m <= A[k]`
  * membership       : `∃ i < a.size, result = a[i]!`
                       -> `Exists k. 0 ≤ k < n ∧ m == A[k]`
Together they pin `m` to be exactly the minimum value (a lower
bound that is itself attained), matching VERINA's postcond with no
weakening.  VERINA's `a[i]!` (panicking indexing) is total here
because the quantifier bounds `i < a.size`, so `!` never hits the
default; our `A[k]` for `0 ≤ k < n` is the same in-bounds access.

Same shape / atom space as corpus `array_min_val` (single-pass
min-value scan: init `m, i := A[0], 1`; SB(n=2) body keeps the
smaller of `m` / `A[i]`).  PURE Z3: no uninterpreted function, no
axioms, no Lean dispatch — the invariant "`m` is the min of prefix
[0, i) AND equals some element of it" is expressible with two
quantified tau atoms, so Z3 discharges the whole obligation.

TRUST SURFACE: none beyond Z3.  No axioms; the result rests only on
the SMT solver's discharge of the loop invariant / coverage /
termination obligations.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 1), "
        "return the minimum value among A[0], A[1], ..., A[n-1]."
    ),

    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    locals   = [Var("i", "int", "local")],

    pre      = "n >= 1",
    # VERINA postcond: minimum value = attained lower bound.
    post     = (
        "ForAll(lambda k: Implies(0 <= k and k < n, m <= A[k])) and "
        "Exists(lambda k: 0 <= k and k < n and m == A[k])"
    ),

    atoms = {
        # Entry: m, i := A[0], 1   (mirrors VERINA's `loop a 1 (a[0]!)`)
        "s@B0": [{"m": "A[0]", "i": "1"}],

        "tau@L0": [
            "1 <= i",
            "i <= n",
            "n >= 1",
            # m is a lower bound on the scanned prefix [0, i) ...
            ("ForAll(lambda k: Implies("
             "0 <= k and k < i, m <= A[k]))"),
            # ... and m is attained within that prefix.
            ("Exists(lambda k: 0 <= k and k < i and m == A[k])"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0 (A[i] < m): m := A[i]; advance.
        "g@B1.0": ["A[i] < m"],
        "s@B1.0": [{"m": "A[i]", "i": "i + 1"}],
        # Branch 1 (A[i] >= m): keep m; advance.
        "g@B1.1": ["A[i] >= m"],
        "s@B1.1": [{"i": "i + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_75/lean/SynthLean/Y2Corpus/verina_basic_75",
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
