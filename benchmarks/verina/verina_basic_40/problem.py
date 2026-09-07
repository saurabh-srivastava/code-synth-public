"""verina_basic_40 — secondSmallest (array -> scalar).

Port of VERINA task `verina_basic_40` (secondSmallest), upstream
dafny-synthesis task_id_755.  Return the second-smallest DISTINCT
value in an integer array.

VERINA source of truth
-----------------------
signature: secondSmallest (s : Array Int) : Int

precond:
    s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!
      -- at least two elements AND at least two distinct values.

postcond (over `result`):
    (∃ i, i < s.size ∧ s[i]! = result) ∧
    (∃ j, j < s.size ∧ s[j]! < result ∧
      ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)

Reading of the postcond: `result` is an array element (conj 1); and
there is an element s[j] strictly below `result` such that every
element NOT equal to s[j] is ≥ result (conj 2).  s[j] is therefore the
minimum, and `result` is the smallest value strictly above the
minimum — i.e. the second-smallest DISTINCT value.

Modelling / fidelity
--------------------
- `s : Array Int`  → array `A` + explicit length `n` (= `s.size`).
- Nat index bounds (`i : Nat`, so `0 ≤ i`) are written explicitly.
- `s[i]!` on a valid index (`i < s.size`) is the element value → `A[i]`.
- Bool: n/a (return type is Int).
- pre `s.size > 1` → `n >= 2`; the distinctness ∃ is carried verbatim
  (single multi-var `Exists(lambda p, q: ...)`).
- post is transcribed atom-for-atom over output `result` (the two
  conjuncts, including the ∃j ∀k quantifier alternation).

This is a PURE-Z3 benchmark: the spec is fully first-order over the
Z3 array `A`; no uninterpreted fold/count function is required, so
there is NO axiom trust surface (trust_axioms = []).

Algorithm synthesized (single pass, min + second-min + found flag)
------------------------------------------------------------------
    m, sm, found, i := A[0], A[0], 0, 1
    while i < n:
        if   A[i] < m:  sm, m, found := m, A[i], 1     # new min; old min → second
        elif A[i] > m:  sm := (A[i] if found==0 or A[i]<sm else sm); found := 1
        else:           pass                            # duplicate of the min
        i += 1
    result := sm

The loop invariant is the standard disjunctive flag-fold (cf.
`all_positive`, `is_sorted`) crossed with two-value tracking (cf.
`min_max_pair`):

  (found==0 ∧ ∀k<i. A[k]==m)                       # only one value seen
  ∨
  (found==1 ∧ m<sm ∧ ∀k<i.(A[k]==m ∨ A[k]≥sm)      # two-plus values seen
             ∧ ∃k<i.A[k]==m ∧ ∃k<i.A[k]==sm)

At exit i==n the `found==0` disjunct is refuted by the precondition's
distinctness ∃ (two distinct values ⇒ not all-equal), forcing
found==1, from which both post conjuncts (with result==sm) follow.
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    description = (
        "Given an integer array A of length n (n >= 2) that contains "
        "at least two distinct values, return the second-smallest "
        "distinct value: the smallest element that is strictly larger "
        "than the minimum element."
    ),

    template = SB() >> Loop(SB(n=3)) >> SB(),
    inputs   = [Var("A", "int[]", "input"),
                Var("n", "int", "input")],
    outputs  = [Var("result", "int", "output")],
    locals   = [Var("m", "int", "local"),
                Var("sm", "int", "local"),
                Var("found", "int", "local"),
                Var("i", "int", "local")],

    pre  = ("n >= 2 and "
            "Exists(lambda p, q: 0 <= p and p < n and 0 <= q and q < n "
            "and A[p] != A[q])"),

    post = (
        "Exists(lambda i: 0 <= i and i < n and A[i] == result) and "
        "Exists(lambda j: 0 <= j and j < n and A[j] < result and "
        "  ForAll(lambda k: Implies(0 <= k and k < n and A[k] != A[j], "
        "                           A[k] >= result)))"
    ),

    atoms = {
        # m, sm, found, i := A[0], A[0], 0, 1
        # sm seeded to A[0] (== m) so the found==0 disjunct is the one
        # that holds initially (m < sm is false).
        "s@B0": [{"m": "A[0]", "sm": "A[0]", "found": "0", "i": "1"}],

        "tau@L0": [
            # KEY disjunctive flag-fold invariant over prefix [0, i).
            ("((found == 0) and "
             " ForAll(lambda k: Implies(0 <= k and k < i, A[k] == m))) or "
             "((found == 1) and (m < sm) and "
             " ForAll(lambda k: Implies(0 <= k and k < i, "
             "                          A[k] == m or A[k] >= sm)) and "
             " Exists(lambda k: 0 <= k and k < i and A[k] == m) and "
             " Exists(lambda k: 0 <= k and k < i and A[k] == sm))"),
            "1 <= i",
            "i <= n",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # Branch 0: A[i] < m  → new minimum; old min becomes second.
        "g@B1.0": ["A[i] < m"],
        "s@B1.0": [{"m": "A[i]", "sm": "m", "found": "1", "i": "i + 1"}],
        # Branch 1: A[i] > m  → candidate second-smallest.
        #   found==0 : first distinct value above the min → sm := A[i].
        #   found==1 : tighten to the smaller of the two.
        "g@B1.1": ["A[i] > m"],
        "s@B1.1": [{
            "sm": "A[i] if (found == 0 or A[i] < sm) else sm",
            "found": "1",
            "i": "i + 1",
        }],
        # Branch 2: A[i] == m → duplicate of the min; advance only.
        "g@B1.2": ["A[i] == m"],
        "s@B1.2": [{"i": "i + 1"}],

        # Final: result := sm.
        "s@B2": [{"result": "sm"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_40/lean/SynthLean/Y2Corpus/verina_basic_40",
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
