# L1.5 — Karstadt-Schwartz fewer-additions Strassen

Goal: 2×2 × 2×2 matrix multiplication has a fixed bilinear-rank
lower bound of **7 multiplications** (Strassen 1969; Winograd
1971; tightness via De Groote 1978).  Within that fixed K=7,
the open question is the **minimum number of additions** in the
linear combinations.

## Counting convention

Each bilinear product takes the shape
`m_k = (Σ_i α[k][i] · A_i) × (Σ_i β[k][i] · B_i)` and each output
is `C_j = Σ_k γ[j][k] · m_k`.  With ±1 coefficients, a linear
combination with `n` nonzero entries needs `n - 1` additions
(or subtractions, counted the same).

**Total additions** = `Σ_k (|α_k| - 1) + Σ_k (|β_k| - 1) +
Σ_j (|γ_j| - 1)` = `Σ|α| + Σ|β| + Σ|γ| - 18`
(since 7 + 7 + 4 = 18 linear forms total).

Equivalently we minimize **total nonzero coefficient count**
across all three tensors.

## Known baselines

| Algorithm        | Year | Σ|nz| | Additions | Notes                                       |
| ---              | ---  | ---:  | ---:      | ---                                         |
| Strassen         | 1969 | 36    | 18        | Original asymmetric form                    |
| Winograd         | 1971 | 33    | 15        | Symmetric form; minimum over ±1 coefs (Heun) |
| Karstadt-Schwartz| 2017 | —     | 12        | Uses shared sub-expressions (λ-algorithm)   |

Heun 1994 proved 15 is optimal for K=7 ±1-coefficient algorithms
**without common sub-expressions**.  Karstadt-Schwartz's 12
exploits common sub-expression sharing (CSE), reducing the
count to 12 across all linear forms but at the cost of a more
complex algorithm structure.

## Framework approach

This problem aligns with the framework's confirmed strengths:

1. **Small bilinear tensor** (4×4×4 = 64 constraints).
2. **Search dim ~168 booleans** for ±1 coefficient choices —
   well within the verified sweet spot (~200 vars).
3. **MaxSAT minimization** via `Z3 Optimize()` with soft
   constraints on each position.
4. **Structural-class speculation** as fallback if direct search
   wedges.

## Plan

### Phase A — verify baselines

A1. Z3 polynomial-identity check on Strassen's 7-mult witness
    (18 adds).  Sanity: confirms tensor encoding correct.
A2. Z3 polynomial-identity check on Winograd's 7-mult witness
    (15 adds).
A3. Verify the canonical 2×2 matmul tensor matches our
    target_tensor() construction.

### Phase B — direct MaxSAT for ±1 coefs without CSE

B1. Z3 Optimize with soft constraints minimizing total nonzero
    coefficients; expect minimum = 33 (Winograd, 15 additions).
B2. Z3 SAT at threshold ≤ 14 additions (= ≤ 32 nonzeros):
    expected UNSAT (Heun lower bound).  This re-derives Heun's
    bound by independent Z3-kernel verification.
B3. Sweep additions ∈ {18, 17, ..., 12}: tabulate SAT/UNSAT at
    each.  Lean-axiomatizable narrative for each threshold.

### Phase C — CSE extension (toward Karstadt-Schwartz 12)

C1. Extend encoding to allow `L` shared sub-expressions
    (intermediate linear forms used in multiple `m_k`).
C2. Search for ≤ 12 additions with CSE allowed.  Verify the
    Karstadt-Schwartz witness independently.
C3. Search for ≤ 11 additions with CSE: if UNSAT, novel Z3-checked
    lower bound at the CSE-allowed Strassen-style class.

### Phase D — structural narrative

If direct search wedges at some threshold, enumerate
structural classes (e.g., specific symmetry patterns,
fixed subsets of mults to fix Strassen-style) and run
Lean-axiomatized speculation for fast UNSAT verdicts.

## Status

- [x] A1 — Strassen K=7 witness verified (Σ|nz| = 36, 18 adds).
- [-] A2 — Winograd K=7 witness; deferred (literature lookup needed
       for ±1 form, may not exist at our literal-form counting).
- [x] B1 — **Threshold sweep ±1-coef Σ|nz|**.  Results:

      | Threshold | Verdict   | Time     | Notes                    |
      | ---       | ---       | ---      | ---                      |
      | 36        | **SAT**   | 31s      | Strassen-equivalent witness |
      | 35        | **WEDGE** | > 1700s  | Z3 internal-timeout did not return; shell-killed at 1800s |
      | 34        | **UNSAT** | 288s     | Z3-checked lower bound   |
      | 33        | **UNSAT** | 199s     | Z3-checked lower bound   |

       **Minimum literal Σ|nz| ≥ 35** (from definitive UNSAT at 34).
       Whether 35 is achievable or 36 (= Strassen) is the actual
       minimum remains **undetermined within framework reach**.
       Z3 Optimize() returned UNKNOWN at 29min budget; the direct
       per-threshold binary-search sweep wedged at 35 specifically
       — the SAT/UNSAT boundary.

- [x] B2 — Z3-kernel-checked lower bound ≥ 35 on literal nonzero
       count.  This is **distinct from** Heun's 15-add SLP bound
       (Heun counts SLP additions with CSE; we count literal
       bilinear-form coefficient nonzeros — see Phase C).

- [x] C1 — `slp_forms.py`: minimum-SLP encoder for a fixed set of
       ±1 linear forms.  Uses linear (QF_LIA) boolean encoding via
       1-hot source pickers; no NIA.

- [x] **C-decoupled — Strassen 1969 SLP decomposition** (Z3-kernel-checked):

      | Side    | Forms   | Min SLP | Time (UNSAT) |
      | ---     | ---     | ---:    | ---          |
      | α (left)  | 7 forms over 4 inputs | **5** | 0.31s (L=5 SAT after L=4 UNSAT in 0.18s) |
      | β (right) | 7 forms over 4 inputs | **5** | 0.13s |
      | γ (output)| 4 forms over 7 inputs | **8** | L=7 UNSAT 186s; L=8 SAT 49s |

       **Total Strassen SLP = 18**.  Matches the standard count
       exactly.  Our framework re-derives this independently.

- [x] C-joint — Joint bilinear + SLP encoder (`encoding_joint.py` +
       `search_joint.py`).  **CONFIRMED WEDGE**:

      | Split                | Total | Verdict   | Time     |
      | ---                  | ---:  | ---       | ---      |
      | (5, 5, 8) Strassen   | 18    | **TIMEOUT** | 500s   |
      | (4, 4, 4) K-S target | 12    | **TIMEOUT** | 1700s  |

       The joint encoder's combined search space (168 bilinear
       booleans + L_total × 24 SLP variables + Int unfolding
       constraints) exceeds the framework's verified
       ~200-variable wedge limit.  Even the SANITY check
       (Strassen at 18) doesn't return in budget.

       This is a clean instance of the documented framework
       wedge — joint SLP+bilinear search past the sweet spot.

- [x] D — **Structural enumeration (L1.2-pattern).**
       `phase_d_enumerate.py` SAT-blocks distinct K=7 ±1 witnesses
       at Σ|nz| ≤ 36, computing per-side SLP costs for each.
       Results (5 witnesses enumerated):

      | # | Σ|nz| | SLP_α | SLP_β | SLP_γ | Total | Search time |
      |---|------:|------:|------:|------:|------:|---:         |
      | 1 |    36 |     5 |     5 |     8 |  **18** | 31s       |
      | 2 |    36 |     5 |     5 |     8 |  **18** | 186s      |
      | 3 |    36 |     5 |     5 |     8 |  **18** | 330s      |
      | 4 |    36 |     5 |     5 |     8 |  **18** | 0.01s     |
      | 5 |    36 |     5 |     5 |     8 |  **18** | 0.01s     |

       **All 5 distinct witnesses have total SLP cost = 18.**
       Witnesses #4-5 found instantly after blocking #3 — sign-flip
       / output-permutation variants caught by the incremental
       solver.  Witnesses #1-3 are structurally distinct.

       Per-side costs identical across all witnesses:
       α=5 (each Strassen-style 5 binary adds), β=5, γ=8.

       This is the framework's certified result: **across enumerated
       ±1 K=7 bilinear decompositions, minimum total SLP cost = 18**.
       Note: only the lex-ordering permutation symmetry is broken;
       a stronger sym-break (transpose, sign-flip canonicalization)
       would reduce iter 4-5's redundant witnesses.

## Final findings

### Z3-kernel-checked results

1. **Strassen 1969 verified** as a K=7 ±1-coefficient bilinear
   decomposition of 2×2 matmul: Σ|nz| = 36, total 18 binary
   adds (5 + 5 + 8 on α + β + γ sides).

2. **Literal-form ±1 Σ|nz| lower bound ≥ 35** (definitively from
   the UNSAT result at threshold 34).  Likely = 36, pending the
   threshold-35 search settling.

   This is a distinct metric from Heun/Probert's 15-add SLP
   bound.  Heun counts binary additions in a straight-line
   program with shared sub-expressions; our literal count sums
   nonzero coefficients in the bilinear-form decomposition.

3. **Strassen's straight-line program length = 18** confirmed
   via independent per-side minimum-SLP search (slp_forms.py):
   - α-side min SLP = 5 (Strassen's value, optimal).
   - β-side min SLP = 5 (optimal).
   - γ-side min SLP = 8 (optimal: L=7 UNSAT).

### Framework wedge points

1. **Joint bilinear + SLP encoder wedges past sweet spot.**
   Even sanity check on Strassen's (5, 5, 8) split times out at
   500s.  The joint search space (168 bilinear booleans + L_total
   × 24 SLP variables + Int unfolding constraints) exceeds the
   framework's verified ~200-variable wedge limit.

   Confirms the compact reminder: "Direct rank-1 SAT past ~300
   booleans/200 constraints wedges".  Joint SLP+bilinear is
   another instance.

2. **Z3 Optimize() returned UNKNOWN at 29min** on the bilinear-
   form min-Σ|nz| problem.  The direct per-threshold sweep
   approach (used here) was strictly more reliable.

### Open follow-ons

1. **Winograd ±1 search at Σ|nz| > 36.**  Winograd's classical
   15-add algorithm uses 4-term coefficient combinations (e.g.,
   `a + b + c - d`) in some bilinear forms.  Σ|nz| under our
   counting would be > 36 because of multi-term entries.  Our
   bilinear-form search at threshold ≤ 36 wouldn't find it.
   Extending the search to threshold ≤ 45 (or so) and running
   slp_forms on each witness would tell us if a 15-add ±1
   variant is reachable.

2. **Stronger sym-break for Phase D.**  Iterations 4-5 found
   trivial sign-flip variants instantly.  Adding canonical
   forms (positive-leading mult coefs, lex-order outputs) would
   eliminate redundant witnesses and let us enumerate further
   structurally-distinct witnesses faster.

3. **L1.5-extension via Lean-axiomatized speculation (K-S 12).**
   The K-S 12-add target needs CSE across the γ-side
   computation.  A speculation class "fixes Strassen's bilinear
   coefs + searches γ-SLP with budget 5 (instead of 8)" — this
   already ran via slp_forms.py and is UNSAT (L=7 UNSAT confirmed).
   To reach K-S 12, the bilinear coefs themselves must differ
   from Strassen's (admitting 4-term linear forms that share via
   CSE).  This requires the Winograd-style search above.
