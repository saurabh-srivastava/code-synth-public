# L3.1 — Sorting networks at small N (open frontier)

A **sorting network** on N wires is a fixed sequence of compare-
exchange operations:
```
CE(i, j):  (w[i], w[j])  ←  (min(w[i], w[j]), max(w[i], w[j]))
```
The sequence is data-independent: same comparators in the same
order, always.  Question: minimum number of comparators needed to
guarantee a sorted output for every input?

## Known minima (OEIS A003075)

| N  | min comparators | Closed by                       |
| -- | ---:            | ---                             |
| 2  |   1             | trivial                         |
| 3  |   3             | trivial                         |
| 4  |   5             | classical                       |
| 5  |   9             | classical                       |
| 6  |  12             | Knuth Algorithm 5.3.4           |
| 7  |  16             | classical                       |
| 8  |  19             | Bose-Nelson 1962                |
| 9  |  25             | **Codish-Cruz-Filipe 2014** (SAT) |
| 10 |  29             | **Bundala-Závodný 2014** (SAT)   |
| 11 |  ≤ 35           | **OPEN** below 35              |
| 12 |  ≤ 39           | **OPEN** below 39              |

Bundala-Závodný 2014 was the LAST sorting-network closure for
small N.  N=11 and N=12 still have gaps between best-known
upper bounds and SAT-proven lower bounds.

## Framework match

This is the first L3 problem family — straight-line-program
with slots, simulated on `{0, 1}^N` per the zero-one principle.

For N=11, C=35:
  - has-bools: 35 × C(11, 2) = 35 × 55 = 1925
  - wire-bools: 2^11 × 35 × 11 ≈ 790,000
  - 1-hot + sortedness + propagation constraints

Larger than our verified ~200-variable sweet spot for hard rank-1
SAT, but pure-boolean propagation is fundamentally easier — modern
SAT solvers handle million-variable instances routinely.  Z3's
internal SAT may or may not scale; Codish et al. used MiniSat /
Glucose.

## Phases

### Phase A — encoding + N≤8 baselines

A1. Z3 SAT encoding via 0/1 principle (`encoding.py`).
A2. Symmetry breaking: disjoint-wire-set commutativity
    + first-comparator = (0, 1) canonicalization.
A3. Verify known optima for N=4..8 (smoke tests).

### Phase B — N=9, N=10 reproductions

B1. Reproduce N=9 = 25 (Codish-Cruz-Filipe 2014).
B2. Reproduce N=10 = 29 (Bundala-Závodný 2014).
B3. Confirm UNSAT at N=9 C=24, N=10 C=28 (lower bounds).

### Phase C — N=11 attack (genuine open frontier)

C1. Search N=11 at C=34, descending — first SAT is new
    upper bound below 35.
C2. UNSAT at C=33 (the SAT-proven lower bound) would close
    N=11 at 34 (matching the lit-bound from Codish 2014).
C3. UNSAT at C below the Codish 2014 lower bound would
    improve the known lower bound — but unlikely with Z3.

### Phase D — L1.2-pattern structural narrative

D1. Speculate over starting prefixes (first 5 comparators
    fixed to a known sub-network from N=10's optimum).
D2. Search residual; produce a comprehensive "every
    Bose-Nelson-prefix-derived extension UNSAT below X"
    narrative.

## Status

- [x] A1 — Z3 SAT encoding.
- [x] A2 — sym break (disjoint commute + first CE = (0, 1)).
- [x] A3 partial — N=4 (C=5 SAT 0.03s, C=4 UNSAT 0.02s);
       N=5 (C=9 SAT 0.24s); N=6 (C=12 SAT 65s).
- [✗] **A3 — N=7 (C=16), N=8 (C=19): WEDGED on Z3.**  Both
       searches consumed > 10 min CPU each with no verdict
       returned.  Z3's SAT engine doesn't scale for this
       large pure-Boolean propagation problem with our
       current encoding.
- [-] **PIVOT**: see L3.4 branchless codegen instead.  Codish-
       Bundala-Závodný used MiniSat / Glucose via DIMACS export,
       not a general SMT solver — different tool category.
       Z3's BV theory shines elsewhere.

## Pivot rationale

Sorting-network SAT problems at N=7+ have:
  - ~340 has-booleans + ~30K wire booleans (for N=8, C=19).
  - ~30K propagation constraints (one per (input, slot, wire)).

Pure-Boolean SAT of this scale is solved daily by MiniSat /
Glucose / CaDiCaL.  Z3's SAT engine is tuned for SMT
instances where the bulk of reasoning is theory-specific
(arithmetic, BV, arrays) — it underperforms dedicated SAT
solvers on combinatorial propositional search.

Two options to revisit later:
  1. Export to DIMACS, invoke an external SAT solver
     (substantial framework extension; not aligned with our
     Z3-direct pattern).
  2. Use stronger structural symmetry breaking (Codish et al.
     layered-canonical-form) — narrows search 100×.

For now, **L3.1 sorting networks** stay parked at the
small-N validation, demonstrating the L3.0 IR pattern works
mechanically.  The IR investment carries forward to other
L3 targets that fit Z3 better.

## Smoke results (Phase A)

| N | C  | Verdict | Time   | Notes              |
| - | -- | ---     | ---    | ---                |
| 4 |  5 | SAT     | 0.03s  | known minimum      |
| 4 |  4 | UNSAT   | 0.02s  | confirms lower bd  |
| 5 |  9 | SAT     | 0.24s  | known minimum      |
| 6 | 12 | SAT     | 65s    | known minimum      |
| 7 | 16 | running |        | budget 1100s       |
| 8 | 19 | running |        | budget 1700s       |
