# L3.4 — Branchless code synthesis (SLP over bitvectors)

Search for the minimum-length straight-line program (SLP) of
bitvector operations that computes a target specification.  This is
the second L3 problem family, fitting the SLP-with-slots IR (L3.0)
established for sorting networks but mapping to Z3's BV theory
where Z3 shines.

## Op alphabet (current — extensible)

  - **1-arg**: NEG, NOT, SAR_W1 (arithmetic-shift-right by W-1),
    SHL1, SHR1, SHL2, SHR2.
  - **2-arg**: ADD, SUB, XOR, AND, OR, LSHR (variable shift).

13 ops total.  No constants; shifts by 4+ (relevant at W=8) require
chained SHR2.

## Encoding

  - Each slot k ∈ [0, C): 1-hot over the 13 ops; 1-hot src1, src2
    pickers over `{x_0, ..., x_{n-1}, s_0, ..., s_{k-1}}`.
  - Correctness: exhaustive over `{0, ..., 2^W-1}^n` inputs.  Each
    concrete input gives one substituted BV expression for the
    final slot; assert it equals `spec(x_vals)`.

## Results

| Spec        | Width | Inputs | Min C | Time     | UNSAT lower bd | Form                         |
| ---         | ---:  | ---:   | ---:  | ---      | ---            | ---                          |
| abs4        | 4     | 1      | **3** | 0.21s    | C=2 (60ms)     | `(x ^ (x>>W-1)) - (x>>W-1)` (textbook) |
| abs8        | 4→8   | 1      | **3** | 3.78s    | C=2 (560ms)    | same form, 8-bit             |
| sign4       | 4     | 1      | **4** | 1.58s    | C=3 (350ms)    | non-textbook: 2× SAR + 2× SUB |
| isnonzero4  | 4     | 1      | **4** | 3.70s    | C=3 (290ms)    | `-((x \| -x) >> W-1)` (textbook) |
| avg4u       | 4     | 2      | **4** | 44s      | C=3 (14.6s)    | `(a & b) + ((a ^ b) >> 1)` (textbook HD) |
| popcount4   | 4     | 1      | ≥ 5   | C=4 UNSAT (7.8s) | —           | C=5 search wedges at 60s     |
| parity8     | 8     | 1      | ≥ 4   | C=3 UNSAT (62s)  | —           | needs SHR4 for log₂ tree fold |
| min4u       | 4     | 2      | ≥ 4   | C=3 UNSAT (10s)  | —           | C=4 search wedges at 120s    |

## Highlights

### sign4 rediscovery (non-textbook 4-op variant)

```
s0 = SAR_W1(x)        // -1 if x<0 else 0
s1 = SUB(s0, x)       // s0 - x
s2 = SAR_W1(s1)       // sign-extend s1
s3 = SUB(s0, s2)      // result
```

Textbook is `(x >> W-1) | (-x >>u W-1)` (4 ops: SAR, NEG, LSHR,
OR).  Z3 found a different 4-op shape using only SAR + SUB.
**Framework-discovered SLP variant** — Z3-checked to be valid
on all 16 inputs.

### avg4u — textbook HD recipe rediscovered + lower bound

Hacker's Delight gives `(a & b) + ((a ^ b) >> 1)` for the
overflow-free average without justification of minimality.  Our
search:
  - C ≤ 3: UNSAT (14.6s) — proven minimum is **4**.
  - C = 4: SAT (44s) — finds the textbook form exactly.

This is the framework's first **Z3-kernel-checked optimality
result** for an HD-style branchless kernel — modest but novel
contribution.

## Limits surfaced

  - **popcount4** wedges at C=5 with current alphabet.  SWAR-style
    construction needs constants (`0x5`, `0x3`) which our alphabet
    lacks.  Without masks, popcount is fundamentally harder.
  - **parity8** at C=3 UNSAT.  Standard 3-op log₂ tree
    (`x ^= x>>4; x ^= x>>2; x ^= x>>1`) needs SHR4, not in
    alphabet.  With SHR4 added, expect C=4 SAT (3 XORs + 3 shifts
    chained → 6 ops in our alphabet; or with SHR4 directly: 3+3=6).
  - **min4u** wedges at C=4.  Branchless unsigned min needs
    `b ^ ((a^b) & -(a<b))` or signed-diff trick.  Limited by 2-input
    × 256-pair search × 13-op alphabet.

## Future extensions

  1. **Add constants** (`CONST_0`, `CONST_1`) to alphabet — **DONE**
     (commit pending).  Sanity passes; popcount4 still wedges at C=5
     (Z3 timeout); parity8 at C=3 takes 92s and remains UNSAT.
  2. **Add SHR4** for k-bit shifts at wider W — **DONE** (commit
     pending).  Doesn't unlock parity8 in framework reach.
  3. **AlphaTensor-style joint SLP+bilinear search** — retrofits to
     L1.5 K-S 12-add attack.  (L3.8 in OPEN_PRBS.)  Would require
     Lean-axiomatized bilinear identity + Z3-searched SLP overlay.

## Parking rationale

L3.4 demonstrated the SLP-with-BV-ops IR mechanically — abs/sign/
isnonzero/avg rediscoveries land cleanly.  But popcount/parity at
their canonical widths (4-bit, 8-bit) wedge on direct Z3 SAT
search even with extended alphabet — Z3's BV theory plus exhaustive
input enumeration produces large QF_BV instances that hit the
framework's documented wedge limit.

Per the guiding principle (CLAUDE.md "Lean axiomatize + Z3 shim,
NOT pure Z3 SAT search past the wedge limit"), this thread
exercised pure-Z3 search past where it's appropriate.  L3.4 is
parked as documented IR validation.  Future L3.4 deliverables
should use Lean-axiomatized sub-circuits + small Z3 residuals
(e.g., for popcount, axiomatize specific SWAR sub-circuits as
Lean theorems and search for how to compose them).

## Status

- [x] Encoding + first 5 rediscoveries (abs4, abs8, sign4,
       isnonzero4, avg4u).
- [x] Z3-checked optimality at small C for above.
- [x] sign4 framework-discovered non-textbook variant.
- [x] avg4u — first Z3-checked HD-recipe optimality proof.
- [x] Alphabet extension (CONST_0, CONST_1, SHR4) — landed but
       doesn't unlock popcount4/parity8 within framework reach.
- [-] popcount4 / parity8 / min4u — wedge with extended alphabet;
       confirms framework limit on direct BV SAT search.
- [✗] **PARKED.** Future L3.4 work should use Lean-axiomatized
       SWAR-sub-circuit speculation, not raw Z3 search.
