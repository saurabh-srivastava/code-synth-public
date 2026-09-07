"""verina_basic_44 (isOddAtIndexOdd) — VERINA-basic port.

Check whether every ODD index of an integer array holds an ODD value.
Returns 1 (true) if, for every index i that is odd, A[i] is also odd;
0 (false) otherwise.

VERINA spec (from datasets/verina/verina_basic_44/task.lean, between
the @start/@end markers; source of truth):
    signature : isOddAtIndexOdd (a : Array Int) -> Bool
    aux       : isOdd (n : Int) : Bool := n % 2 == 1
    precond   : True
    code      : (a.mapIdx fun i x => (i, x)).all
                  (fun (i, x) => !(isOdd i) || isOdd x)
    postcond  : result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))

Port / fidelity mapping
-----------------------
    Pre  : n >= 0            (n = a.size; Array size is a Nat, hence
                              n ≥ 0.  VERINA precond is `True`; the
                              n ≥ 0 fact is the only content of the
                              Array-size Nat and is needed by the loop
                              invariant.)
    Post : ((result == 1) and ∀k. 0 ≤ k < n ⇒ (isOdd k ⇒ isOdd A[k])) or
           ((result == 0) and ∃k. 0 ≤ k < n ∧ isOdd k ∧ ¬ isOdd A[k])

    VERINA output var `result : Bool` -> our output var `result : int`
    with the Bool→{0,1} convention (1 = true, 0 = false).
    VERINA `isOdd(x) := x % 2 == 1` -> our `x % 2 == 1` verbatim
    (see fidelity note on `%` semantics below).

SPEC-FIDELITY NOTE
------------------
VERINA's postcond is the biconditional `ALLODD ↔ result`, where
`ALLODD ≡ ∀ i < a.size, isOdd i → isOdd a[i]` and
`isOdd(x) ≡ x % 2 == 1`.  Our post writes the SAME biconditional in
explicit case-split form over a {0,1}-valued `result`:
  * `result == 1  ⇒  ALLODD`            (the `(result==1) ∧ ALLODD` disjunct)
  * `result == 0  ⇒  ¬ALLODD`           (the `(result==0) ∧ ∃-witness` disjunct)
`¬ALLODD` over the indices is exactly "∃ an odd index k with A[k] not
odd" — the literal De Morgan dual of the ForAll disjunct (the negation
of `isOdd k → isOdd A[k]` is `isOdd k ∧ ¬ isOdd A[k]`).  Given
`result ∈ {0,1}`, `(1 ∧ ALLODD) ∨ (0 ∧ ¬ALLODD)` is logically
equivalent to `ALLODD ↔ (result == 1)` — a faithful transcription of
VERINA's `↔`.

`isOdd` / `%` semantics.  VERINA's `x % 2 == 1` uses Lean's `Int.emod`
(the `%` operator on `Int`), which returns a remainder in `[0, 2)` for
the positive divisor 2.  Z3's integer `%` uses the same Euclidean
convention (result in `[0, 2)` for a positive divisor), so
`x % 2 == 1 ⟺ x odd` holds identically in both Z3 and Lean for every
integer including negatives (e.g. `-3 % 2 == 1`, `-4 % 2 == 0` in both).
The odd-index test `isOdd k` is applied to non-negative indices, where
the two conventions coincide trivially.  So the port is faithful for
all inputs.

Empty-array corner case matches VERINA: n = 0 -> `0 ≤ k < 0` is
unsatisfiable -> ForAll vacuously true, Exists false -> result 1
(VERINA's `.all` over an empty indexed array is `true`).

Same shape as corpus `all_positive` / `is_sorted` and sibling
`verina_basic_19_isSorted` (single-pass flag-fold with early-set flag +
branched body).  The per-index predicate is a single-cell test
(`isOdd k → isOdd A[k]`, touching only A[k]) so it mirrors
`all_positive`'s prefix-form invariant rather than is_sorted's
adjacent-pair form.  PURE Z3: no uninterpreted function, no axioms, no
Lean dispatch — the invariant `flag == 1 ⇔ prefix [0,i) has no odd-index
even-value violation` is expressible with a quantified tau atom, so Z3
discharges the whole obligation.

TRUST SURFACE: none beyond Z3.  No axioms; the result rests only on
the SMT solver's discharge of the loop invariant / coverage /
termination obligations.
"""
from synth import Problem, SB, Loop, Var, solve


# Per-index "good" predicate at index k: if k is odd then A[k] is odd.
# Written in explicit disjunctive (De Morgan) form so it parses as a
# plain boolean guard.
def _good(k, ak):
    return f"(({k} % 2 != 1) or ({ak} % 2 == 1))"


def _bad(k, ak):
    return f"(({k} % 2 == 1) and ({ak} % 2 != 1))"


PROBLEM = Problem(
    description = (
        "Given an integer array A and a length n (with n ≥ 0), "
        "return 1 if every odd index k in [0, n) holds an odd value "
        "A[k], otherwise return 0."
    ),

    template = SB() >> Loop(SB(n=2)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("flag", "int", "local"),
                Var("i", "int", "local")],

    pre      = "n >= 0",
    # VERINA postcond `ALLODD ↔ result`, in explicit {0,1} case-split form.
    post     = (
        "((result == 1) and "
        " ForAll(lambda k: Implies("
        "0 <= k and k < n, " + _good("k", "A[k]") + "))) or "
        "((result == 0) and "
        " Exists(lambda k: 0 <= k and k < n and " + _bad("k", "A[k]") + "))"
    ),

    atoms = {
        "s@B0": [{"flag": "1", "i": "0"}],

        "tau@L0": [
            "0 <= i",
            "i <= n",
            "n >= 0",
            # flag is 1 iff prefix [0, i) has no odd-index/even-value
            # violation.
            ("((flag == 1) and "
             " ForAll(lambda k: Implies("
             "0 <= k and k < i, " + _good("k", "A[k]") + "))) or "
             "((flag == 0) and "
             " Exists(lambda k: 0 <= k and k < i and "
             + _bad("k", "A[k]") + "))"),
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: index i is "good" (even index, or odd value) → no
        # flip; advance.
        "g@B1.0": [_good("i", "A[i]")],
        "s@B1.0": [{"i": "i + 1"}],
        # Branch 1: index i is odd but A[i] is even → flag := 0; advance.
        "g@B1.1": [_bad("i", "A[i]")],
        "s@B1.1": [{"flag": "0", "i": "i + 1"}],

        "s@B2": [{"result": "flag"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_44/lean/SynthLean/Y2Corpus/verina_basic_44",
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
