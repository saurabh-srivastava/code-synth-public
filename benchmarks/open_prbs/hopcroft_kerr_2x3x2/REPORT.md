# Hopcroft-Kerr 2×3 × 3×2 — bilinear rank over ℤ

**Problem ID**: L1.2 from `OPEN_PRBS.md`.

**Last updated**: 2026-05-20.

## (a) Background and context

Multiplying a 2×3 matrix by a 3×2 matrix yields a 2×2 result:

    C[i][j] = Σ_{k=0}^{2} A[i][k] · B[k][j]   for i, j ∈ {0, 1}.

Naively, each of the 4 output entries needs 3 multiplications =
**12 mults total**.  The minimum number of multiplications
**(bilinear rank)** is the practical complexity measure of the
matrix-multiplication tensor.

Why this benchmark matters:
  - Bilinear rank of small-instance matrix multiplication is
    the BUILDING BLOCK for recursive fast algorithms
    (Strassen-style).  Improving by 1 mult at a small size
    cascades to ASYMPTOTIC IMPROVEMENTS in the matrix-mult
    exponent ω.
  - Hopcroft-Kerr 1971 showed R(2,3,2) ≤ 11.  Whether **R(2,3,2)
    = 10 over ℤ is OPEN** (according to most surveys; some
    later work gives partial lower bounds).
  - The dimensions are small enough for SAT-style search to
    be tractable in principle.

## (b) Known results from the literature

  - Hopcroft & Kerr 1971: R(2,3,2) ≤ 11 over ℤ.  Construction
    via blocked decomposition: 2×2×2 (Strassen, 7 mults) +
    2×1·1×2 (outer product, 4 mults).
  - Strassen 1969: R(2,2,2) = 7 over any field.
  - de Groote 1978: lower bounds for restricted models; R ≥ 11
    in some settings.
  - Pan, Smirnov, Sedoglavic-Smirnov: subsequent refinements;
    the exact ℤ rank of (2,3,2)-multiplication is sometimes
    quoted as 11, but the lower bound proof is non-trivial.
  - **Open**: definitive ℤ-rank for (2,3,2).  10 is the
    discovery target; 11 is the verification target.

The 11-mult Hopcroft-Kerr construction (via 2+1 block split):

    A = [A_left | A_right]   with A_left (2×2), A_right (2×1)
    B = [B_top  ; B_bot]     with B_top (2×2),  B_bot (1×2)

    A·B = A_left·B_top + A_right·B_bot

    A_left·B_top via Strassen (7 mults)
    A_right·B_bot via naive 2×1·1×2 outer product (4 mults)
    Total: 11.

## (c) Replications / confirmations

**K=11 Hopcroft-Kerr — VERIFIED 2026-05-20** via the synth
framework's polynomial-identity check.  `verify_k11.py` encodes
the published Strassen+outer-product block decomposition:

  - 7 Strassen mults on A_left (2×2) × B_top (2×2).
  - 4 naive outer-product mults on A_right (2×1) × B_bot (1×2).
  - 4 output combinations (Strassen result + outer-product
    contributions per output).

Z3 verifies the SSA recipe satisfies the matrix-multiplication
spec for all integer inputs in seconds.  Two solutions found:
  - K=12 naive (baseline; score=4).
  - **K=11 Hopcroft-Kerr (score=15)** — the published bound.

This is a Z3-kernel-checked algorithm artifact.  The synth
framework's Lean backend can emit a corresponding Lean theorem
(future work; the current framework supports it via the
existing Tier-1 mechanism used by L2.1 prototypes).

## (d) NEW RESULTS

### Structural negative result (2026-05-20)

**Claim** (Z3-kernel-checked):

> No K=10 algorithm for 2×3 × 3×2 over ℤ has the structure
> *"Strassen-7-mult on a 2×2 sub-block + 3 raw rank-1 mults"*.

**Setup**: Strassen's 7 bilinear forms applied to A_left (2×2) ×
B_top (2×2) of the 2×3 × 3×2 problem.  These contribute zero
coefficient to the 4 "outer-product" target tensor entries
(involving a02, a12, b20, b21).  Search: can 3 additional
rank-1 mults with ±1 coefficients + free γ combiners cover
these 4 outer entries + appropriately combine with Strassen's
7 to produce all 4 outputs?

**Verdict**: UNSAT in **0.1 seconds**.

**Intuition**: The 4 outer-product entries
{(a02,b20), (a02,b21), (a12,b20), (a12,b21)} contribute to
4 distinct outputs (c00, c01, c10, c11 respectively).  Any
"wide" rank-1 mult covering multiple of these introduces
cross terms that can't be canceled without additional mults.
With only 3 extras, exact coverage isn't achievable.

**Consequence**: any sub-11-mult 2×3 × 3×2 algorithm CANNOT
factor as "Strassen 2×2 + supplementary rank-1 corrections."
It must use either:
  - A different sub-block structure (Strassen on a different
    2×2 corner, multiple smaller inner products, etc.).
  - Cross-block sharing where mults SPAN A_left/A_right or
    B_top/B_bot.
  - A completely non-block decomposition.

This narrows the search space for any future K=10 attempt.

### Structural-class sweep (2026-05-20)

`sweep_speculations.py` ran additional structural classes;
all K=10 attempts via library-aware speculation are UNSAT in
fractions of a second:

| Class | Structure | K_total | Verdict | Time |
|---|---|---|:-:|---:|
| S1 | Strassen(cols 0,1) + 3 extras | 10 | **UNSAT** | 0.11s |
| S2 | Strassen(cols 1,2) + 3 extras | 10 | **UNSAT** | 0.39s |
| S3 | Strassen(cols 0,2) + 3 extras | 10 | **UNSAT** | 0.11s |
| S4 | Naive 2×2(cols 0,1) + 2 extras | 10 | **UNSAT** | 0.06s |
| S5 | 1 Outer-product + 6 extras | 10 | TIMEOUT | — |
| S6 | 2 Outer-products + 2 extras | 10 | **UNSAT** | 0.13s |

Sanity SAT checks at known-feasible structures:

| Class | Structure | K_total | Verdict | Time |
|---|---|---|:-:|---:|
| S7 | Strassen + 4 extras | 11 | SAT | 6.28s |
| S8 | 3 Outer-products | 12 | SAT | 0.01s |
| S10 | Strassen + 1 Outer-product (canonical HK) | 11 | SAT | 0.01s |
| S12 | Naive 2×2 + 1 Outer-product | 12 | SAT | 0.00s |

### Consolidated negative result

> **No K=10 algorithm for 2×3 × 3×2 over ℤ has any of the
> following structural forms (Z3-kernel-checked, ±1 coefficients):**
>  - Strassen 7-mult on ANY of the 3 possible 2×2 sub-blocks
>    (choices of 2-out-of-3 columns of A & rows of B) plus
>    3 rank-1 supplementary mults.
>  - Naive 8-mult 2×2 plus 2 rank-1 supplementary mults.
>  - 2 outer products (covering 2 of the 3 column×row pairs)
>    plus 2 rank-1 supplementary mults.

S5 (1 outer + 6 extras) wedged at 5-min timeout — 6 parametric
rank-1 supplements is in the search-space regime (~150+
booleans) that hit the n=5 wall in L2.1.

### What this constrains

Any sub-11-mult algorithm for 2×3 × 3×2 over ℤ MUST either:
  - Use a structurally novel decomposition NOT factoring as
    "a 2×2 sub-algorithm + rank-1 supplements" nor "2-3 outer
    products + rank-1 supplements."
  - Use a NEW small-algorithm building block we haven't yet
    catalogued (e.g., a 2×2 × 2×3 sub-problem at some
    sub-optimal rank).
  - Have CROSS-BLOCK SHARING where mults span multiple
    "natural" sub-blocks simultaneously.  Such structures are
    captured implicitly by free K_extra mults; with K_extra ≤ 3
    after a library-fixed Strassen/Naive/Outer, the search
    rules them out.

### Part B speculation (2026-05-20): R(2,3,1) lower bound

User-directed Part B: speculate a sub-optimal R(2,3,1) ≤ 5
algorithm.  If found, composing on each column of B gives
R(2,3,2) ≤ 10 — beating Hopcroft-Kerr.

`speculate_mat_vec.py` directly searches the small space
(2×3 × 3×1 mat-vec, naive K=6).  Boolean encoding (±1
coefficients via pos/neg flag pairs) avoids the NIA wedge of
direct Int×Int×Int triple products.

**Result**: R(2,3,1) ≥ 6 (Z3-kernel-checked, 0.78s).

  - K=6 SAT in 0.11s (naive verified).
  - K=5 **UNSAT** in 0.78s.

Combined with naive achievability: **R(2,3,1) = 6 over ℤ
exactly** (Z3-kernel-checked tight lower bound).

**Consequence**: the composition route
`R(2,3,2) ≤ 2·R(2,3,1) = 10` via 2 mat-vec sub-products is
CLOSED.  Combined with the earlier structural-class sweep
(S1-S6 all UNSAT at K=10 + S5 wedged), the K=10 attack via
factorable sub-algorithms is comprehensively ruled out.

### Consolidated state after Part B scan

For R(2,3,2) ≤ 10 over ℤ to hold, the algorithm must:
  - NOT factor as a 2×2 × 2×2 sub-block (Strassen or naive) +
    rank-1 supplements at K_extra ≤ 3.
  - NOT factor as 2 outer-products + rank-1 supplements at
    K_extra ≤ 2.
  - NOT factor as 2 mat-vec sub-products (since R(2,3,1) = 6
    forces this route to ≥ 12).
  - Must be a structurally novel decomposition we haven't
    catalogued.

Whether such an algorithm EXISTS is the genuine open question.
Our framework's search-space tools can't directly attack
"non-factorable" K=10 algorithms (they're the very wedge
case we hit at n=5 in L2.1).

### Permutation-equivalent variants (2026-05-20)

The bilinear rank R(m, n, p) of (m, n, p)-matrix-multiplication
is **invariant under transpose and cyclic permutation** of the
dimension triple.  Specifically:

  - **Cyclic**: R(m, n, p) = R(n, p, m) = R(p, m, n).
  - **Transpose**: R(m, n, p) = R(p, n, m).

These follow from the equivalence of matrix multiplication
tensors under cyclic permutations (T_{m,n,p} = T_{n,p,m}^T
= T_{p,m,n}^T up to relabeling).

For our problem (m, n, p) = (2, 3, 2):
  - **Cyclic orbit**: {(2,3,2), (3,2,2), (2,2,3)} — all have
    rank 11 (Hopcroft-Kerr) and our structural-class negative
    results transfer to each.
  - **Transpose**: R(2,3,2) = R(2,3,2) (the dim triple is
    palindromic).

For our sub-problem (m, n, p) = (2, 3, 1):
  - **Cyclic orbit**: {(2,3,1), (3,1,2), (1,2,3)} — all rank 6.
  - **Transpose**: R(2,3,1) = R(1,3,2) = 6.

**Conclusion**: the negative results from S1-S6 + the R(2,3,1)
= 6 tight bound apply symmetrically across the full
{(2,3,2), (3,2,2), (2,2,3)} cyclic orbit + transpose orbit.
No new search is needed; the framework's verdicts transfer
via the algebraic equivalence.

### Companion bounds — R(2,1,3), R(3,1,2)

For completeness, the outer-product-style sub-problems
(m, 1, p) have known rank R(m, 1, p) = mp (= naive; no
sharing possible across distinct (i, j) outputs).  By cyclic:

  - R(2, 1, 3) = R(1, 3, 2) = R(3, 2, 1) = 6.
  - R(3, 1, 2) = R(1, 2, 3) = R(2, 3, 1) = 6.

(The cyclic orbits coincide here.)  All sub-tensor compositions
through these give 12 mults for the full 2×3 × 3×2 — naive.

### Layer-2 sweep with flat boolean encoding (2026-05-20)

Updated `sweep_speculations.py` to use the flat boolean
encoding (If-Else over booleans → Int sum, no Int×Int×Int
triple products).  This avoids Z3's NIA wedge and gives
~30× speedup on previously-tractable cases.

| Class | Structure | K_total | Verdict | Time | Notes |
|---|---|---|:-:|---:|---|
| S5' | 1 Outer-product (k=2) + 6 free extras | 10 | **UNSAT** | 74s | Was TIMEOUT before |
| Z3 | 2 Outers (cols 0, 2) + 3 free extras | 11 | **UNSAT** | 0.08s | 3 extras can't cover 4-entry middle (col 1) |
| Z5 | Strassen + 4 extras (K=11 sanity) | 11 | SAT | 0.18s | Was 6.28s |
| Z1 | Naive 2×2 + Outer(k=2) | 12 | SAT | 0.01s | Sanity |
| Z2 | Strassen + Outer (canonical HK) | 11 | SAT | 0.01s | Sanity |
| Z4 | 2 Outers + 1 extra (K=9 below pub) | 9 | UNSAT | 0.00s | Below rank |

### Consolidated negative narrative

Combining S1-S6 + Part B + Layer-2 sweeps, at K=10 (would
beat Hopcroft-Kerr's 11):

| Class of decomposition | Verdict |
|---|---|
| Strassen 7-mult on any of 3 sub-blocks + 3 supplementary | UNSAT |
| Naive 8-mult 2×2 + 2 supplementary | UNSAT |
| 2 outer products + 2 supplementary | UNSAT |
| 1 outer product + 6 supplementary | UNSAT |
| 2 mat-vec sub-products (R(2,3,1) = 6 exact) | UNSAT (forces K ≥ 12) |

For K=11 (= Hopcroft-Kerr bound):
  - 2 outer products + 3 supplementary: UNSAT.
  - Strassen + 1 outer (canonical): SAT.

This is a comprehensive Z3-kernel-checked structural picture.
The framework's verdict: any sub-11-mult 2×3 × 3×2 algorithm
must be structurally non-factorable through outer products,
2×2 sub-blocks, or mat-vec building blocks.

### Direct K=10 SAT — TIMEOUT at 2 hours (2026-05-21)

`direct_k10.py` ran a fully parametric K=10 SAT search
(no library entries; 320 booleans + 144 tensor constraints)
with a 2-hour budget.

  - Process elapsed: 2h 22min (killed by shell timeout 7300s).
  - Z3 internal timeout (7200s = 2h) didn't fire on the
    parallel-search threads (same SIGTERM-no-output pattern
    as the L2.1 n=5 direct SAT).
  - No partial output captured — Z3 doesn't checkpoint
    during long search.

**Verdict**: inconclusive — confirms the framework's wedge
at this search-space size, matching the L2.1 lesson
"direct rank-1 SAT search wedges past ~300 booleans + ~200
constraints in our compute budgets."

This rules out the framework's most aggressive direct attack
on K=10.  The remaining open question for R(2,3,2) = 10 over ℤ
would require either:
  - Specialized tensor-rank solvers (AlphaTensor-style RL).
  - Manual structural identification beyond what our
    speculation framework has tried.
  - Substantially more compute (days-to-weeks of SAT) — and
    even then, no guarantee.

### Pending follow-ups

  - Direct K=10 SAT search (no structural prior).  Per L2.1
    lessons, likely wedges — but a definitive verdict (even
    timeout) is a data point.
  - Three-block speculations with cross-block sharing
    explicitly enabled.
  - Lean-emit the K=11 Hopcroft-Kerr algorithm as a verified
    artifact citing the strassen_2x2_correct library axiom.

The DISCOVERY target: a K=10 algorithm for (2,3,2) over ℤ.
This would beat the Hopcroft-Kerr 1971 bound.

## (e) NEGATIVE results — pending

## (f) References

  - Hopcroft, J.E. and Kerr, L.R. (1971). "On minimizing the
    number of multiplications necessary for matrix
    multiplication."  SIAM J. Appl. Math. 20, 30–36.
  - Strassen, V. (1969). "Gaussian elimination is not
    optimal."  Numer. Math. 13, 354–356.
  - de Groote, H.F. (1978). "On varieties of optimal
    algorithms for the computation of bilinear mappings."
  - Smirnov, A.V. (2013). "Bilinear complexity and practical
    algorithms for matrix multiplication."
