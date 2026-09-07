"""verina_basic_54 — CanyonSearch (minimum |a[i] - b[j]| over all pairs).

Ported from VERINA basic task `verina_basic_54` (upstream Clover
`Clover_canyon_search`).  Shape: (Array Int, Array Int) -> Nat.

VERINA spec (source of truth, from task.lean between the
@start/@end markers):

  precond:
      a.size > 0 ∧ b.size > 0
      ∧ List.Pairwise (· ≤ ·) a.toList     -- a sorted non-decreasing
      ∧ List.Pairwise (· ≤ ·) b.toList     -- b sorted non-decreasing

  code (reference): a two-pointer walk `canyonSearchAux` that keeps a
      running minimum `d` of |a[m] - b[n]|, advancing whichever pointer
      points at the smaller element.  Correctness of the *two-pointer*
      shape relies on sortedness.

  postcond:
      (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs)))   -- WITNESS
    ∧ (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))   -- LOWER BOUND

  i.e.  result is the minimum absolute difference over all pairs
  (a[i], b[j]), and some pair attains it exactly.

────────────────────────────────────────────────────────────────────
Our encoding (fidelity claim)
────────────────────────────────────────────────────────────────────
We model `a`, `b` as int-arrays with explicit lengths `n = a.size`,
`m = b.size` (the repo's standard array-with-length convention).  A
Nat result is an int `r`; `|x - y|` is encoded inline as the ternary
`(x - y) if x >= y else (y - x)` (Z3 `If`), so the whole benchmark is
PURE Z3 — no uninterpreted functions, no axioms, no Lean dispatch.

Our POSTCONDITION is VERINA's postcondition verbatim (over pairs
p ∈ [0,n), q ∈ [0,m)):

    Exists p,q. 0<=p<n ∧ 0<=q<m ∧ r == |a[p]-b[q]|            -- a.any/b.any
  ∧ ForAll p,q. 0<=p<n ∧ 0<=q<m ⇒ r <= |a[p]-b[q]|           -- a.all/b.all

so the fidelity of the *specification* is exact.

Our PRECONDITION is WEAKER than VERINA's: we require only `n >= 1 ∧
m >= 1` (both arrays non-empty) and DROP the two sortedness
conjuncts.  This is sound and strengthens the claim: the synthesized
program is the full O(n·m) all-pairs double loop, which computes the
correct minimum for arbitrary (unsorted) inputs — it does not need
sortedness.  VERINA's sortedness precond is only there to justify its
O(n+m) two-pointer shortcut.  Proving correct on a superset of inputs
(all arrays, not just sorted ones) is a strictly stronger result, so
the postcondition is faithfully captured.

Control flow (nested double loop, all-pairs min):

    r, i, wi, wj := |a[0]-b[0]|, 0, 0, 0      // B0 (needs n,m >= 1)
    while i < n:                              // L0 (outer)
        j := 0                                // B1
        while j < m:                          // L1 (inner)
            if |a[i]-b[j]| < r:               // B2 branch 0
                r, wi, wj := |a[i]-b[j]|, i, j
            j := j + 1
        i := i + 1                            // B3
    // post

`wi, wj` are argmin ghost locals: carrying the witness as a CONCRETE
(non-existential) invariant `r == |a[wi]-b[wj]|` keeps the loop
invariants free of an existential, which Z3 discharges far more
reliably; the final Exists postcondition is then instantiated from
`wi, wj`.

Invariants (τ):
  outer L0:  ForAll p,q. p<i ∧ 0<=q<m ⇒ r <= |a[p]-b[q]|   (completed rows)
             ∧ concrete witness ∧ 0<=i<=n ∧ n,m>=1
  inner L1:  ForAll p,q. 0<=q<m ∧ (p<i ∨ (p==i ∧ q<j)) ⇒ r <= |a[p]-b[q]|
             ∧ concrete witness ∧ 0<=j<=m ∧ 0<=i<n ∧ n,m>=1
"""
from synth import Problem, SB, Loop, Var, solve


def adiff(p: str, q: str) -> str:
    """|a[p] - b[q]| as a parenthesised Z3 ternary (pure arithmetic)."""
    return (f"((A[{p}] - B[{q}]) if A[{p}] >= B[{q}] "
            f"else (B[{q}] - A[{p}]))")


# Concrete argmin witness bundle (single conjunctive τ atom).
_WITNESS = (f"0 <= wi and wi < n and 0 <= wj and wj < m "
            f"and r == {adiff('wi', 'wj')}")

# Outer completed-rows lower bound.
_CR = (f"ForAll(lambda p, q: Implies("
       f"0 <= p and p < i and 0 <= q and q < m, "
       f"r <= {adiff('p', 'q')}))")

# Inner lower bound: completed rows (p<i) plus current-row prefix (q<j).
_LB_INNER = (f"ForAll(lambda p, q: Implies("
             f"0 <= p and 0 <= q and q < m and "
             f"((p < i) or (p == i and q < j)), "
             f"r <= {adiff('p', 'q')}))")

# Postcondition — VERINA verbatim (witness ∧ lower bound over all pairs).
_POST = (
    f"Exists(lambda p, q: 0 <= p and p < n and 0 <= q and q < m "
    f"and r == {adiff('p', 'q')}) "
    f"and "
    f"ForAll(lambda p, q: Implies("
    f"0 <= p and p < n and 0 <= q and q < m, "
    f"r <= {adiff('p', 'q')}))"
)


PROBLEM = Problem(
    description = (
        "Given two non-empty integer arrays a and b, return the "
        "minimum absolute difference |a[i] - b[j]| over all index "
        "pairs (i, j).  Some pair attains the returned value exactly."
    ),

    # SB(n=1) >> Loop( SB(n=1) >> Loop(SB(n=2)) >> SB(n=1) )
    template = SB(n=1) >> Loop(SB(n=1) >> Loop(SB(n=2)) >> SB(n=1)),
    inputs   = [Var("A", "int[]", "input"),
                Var("B", "int[]", "input"),
                Var("n", "int", "input"),
                Var("m", "int", "input")],
    outputs  = [Var("r", "int", "output")],
    locals   = [Var("i", "int", "local"),
                Var("j", "int", "local"),
                Var("wi", "int", "local"),
                Var("wj", "int", "local")],

    pre  = "n >= 1 and m >= 1",
    post = _POST,

    atoms = {
        # B0 — init: r, i, wi, wj := |a[0]-b[0]|, 0, 0, 0
        "s@B0": [{"r": adiff("0", "0"),
                  "i": "0", "wi": "0", "wj": "0"}],

        # Outer loop L0.
        "tau@L0": [
            _CR,
            _WITNESS,
            "0 <= i and i <= n and n >= 1 and m >= 1",
        ],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],

        # B1 — inner init j := 0.
        "s@B1": [{"j": "0"}],

        # Inner loop L1.
        "tau@L1": [
            _LB_INNER,
            _WITNESS,
            "0 <= j and j <= m and 0 <= i and i < n and n >= 1 and m >= 1",
        ],
        "g@L1":   ["j < m"],
        "phi@L1": ["m - j"],

        # B2 — inner body SB(n=2): min-update + j++.
        # Branch 0: |a[i]-b[j]| < r  → r, wi, wj := |a[i]-b[j]|, i, j; j++
        "g@B2.0": [f"{adiff('i', 'j')} < r"],
        "s@B2.0": [{"r": adiff("i", "j"),
                    "wi": "i", "wj": "j", "j": "j + 1"}],
        # Branch 1: |a[i]-b[j]| >= r  → j++
        "g@B2.1": [f"{adiff('i', 'j')} >= r"],
        "s@B2.1": [{"j": "j + 1"}],

        # B3 — outer step i := i + 1.
        "s@B3": [{"i": "i + 1"}],
    },

    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    dump_lean_failures_dir = "benchmarks/verina/verina_basic_54/lean/SynthLean/Y2Corpus/verina_basic_54",
    wedge_threshold = 200,
    solver_timeout_ms = 1_800_000,   # 30 min; nested 2D quantified VCs
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
