# Karatsuba over GF(2)[x] — bilinear complexity of polynomial multiplication

**Problem ID**: L2.1 from `OPEN_PRBS.md` (Layer 1 + Layer 2).

**Last updated**: 2026-05-20.

## (a) Background and context

Polynomial multiplication over the binary field GF(2)[x] is a
fundamental operation in:

  - **Cryptography**: AES-GCM authenticated encryption (GHASH
    is GF(2¹²⁸) multiplication, decomposed via polynomial-mult
    primitives); post-quantum schemes (BIKE, HQC, Classic
    McEliece use GF(2)[x] arithmetic at large degrees).
  - **Error-correcting codes**: Reed-Solomon, BCH, and binary
    Goppa codes all reduce to GF(2)[x] arithmetic.
  - **Computer algebra**: factorization of polynomials over
    GF(2), Cantor-Zassenhaus, Berlekamp's algorithm.
  - **Combinatorial design**: GF(2)-linear codes,
    block-cipher S-box construction.

The **bilinear complexity** R(n) of polynomial multiplication
is the minimum number of scalar multiplications (over the
ground field) needed to compute the product of two
polynomials of degree n−1.  Bilinear complexity is the
standard measure of "essential multiplication work" — additions
and constant multiplications are free.

For polynomial multiplication of two degree-(n−1) polynomials:

  - **Karatsuba 1962**: R(2) = 3 (over any field).
  - **Toom-3 1963**: R(3) = 5 over fields with ≥ 5 elements;
    over GF(2), Toom-3 doesn't apply directly (need ≥ n+1
    distinct evaluation points).
  - **General lower bound**: R(n) ≥ 2n − 1 (Strassen 1973,
    via tensor rank arguments).

For GF(2)[x] specifically, the bilinear complexity has been a
subject of focused research because:

  - The naive count is n² multiplications.
  - Karatsuba-style splitting gives n^{log₂3} ≈ n^{1.585}
    multiplications.
  - Over fields with more elements, Toom-Cook gives ~2n−1; over
    GF(2), the exact bilinear rank for small n is intensively
    studied.

Why **L2.1** is interesting for the synthesizer:

  - Bilinear-rank decomposition is a **finite, well-defined**
    optimization problem at each fixed n.
  - The framework's strengths (predicate abstraction + SMT
    search) map naturally to "tensor decomposition over GF(2)".
  - For n ≥ 5, the optimal bilinear rank is **research-active**:
    not all values are tight, and improvements have practical
    crypto implications.

## (b) Known results from the literature

Published bilinear rank values for GF(2)[x] degree-(n−1) ×
degree-(n−1) polynomial multiplication:

| n | Published R(n) over GF(2) | Reference |
| --- | --- | --- |
| 2 | 3 | Karatsuba 1962 |
| 3 | 6 | Cenk-Hasan 2007; Bernstein 2009 |
| 4 | 9 | Cenk-Hasan 2007; Montgomery 2005 |
| 5 | 13 | Cenk-Hasan 2007 |
| 6 | 17 (or 18, depending on construction) | Various |
| 7 | 22 | Cenk-Hasan |
| 8 | 26 | Various |

Lower bounds:

  - 2n − 1 ≤ R(n) (Strassen 1973).
  - For n = 2: 3 (tight).
  - For n = 3: 6 (matches upper bound; proved exact).
  - For n ≥ 4: not all values are proven tight, though
    matched numerical bounds exist.

**Open territory**:

  - n = 5 over GF(2): R(5) ∈ [9, 13].  Whether 12 (or smaller)
    is achievable is partially open.
  - n = 6, 7: rank values not proven tight against published
    upper bounds.
  - Larger n (e.g., crypto block sizes 64, 128): asymptotic
    Karatsuba bounds beat naive; constant-factor improvements
    have ongoing research.

**Practical relevance**: Bernstein's eBATS benchmarks track
the best-known multiplication counts at crypto block sizes
(e.g., 64×64 over GF(2) for GHASH).  Even a small
constant-factor improvement at the right size translates to
measurable AES-GCM throughput gains.

## (c) Replications / confirmations the synthesizer finds

The synthesizer (Z3 SAT search over the tensor-decomposition
encoding) has Z3-kernel-confirmed:

### n=2 (deg-1 × deg-1): R(2) = 3

  - **K=2 UNSAT** (`deg1_discrim_2mult.py`): 4 hand-crafted
    2-mult candidates all rejected.  Confirms the tight
    Strassen lower bound for n=2.
  - **K=3 SAT** (`deg1_verify.py`): Karatsuba 3-mult
    algorithm verifies; the naive 4-mult also verifies.

### n=3 (deg-2 × deg-2): R(3) = 6

  - **K=4 UNSAT** (via `problem.py 3 4`): 0.0s.
  - **K=5 UNSAT** (via `problem.py 3 5` AND `deg2_search5.py`):
    0.0s with symmetry breaking; **0.46s WITHOUT any
    symmetry breaking or pruning** — robust verdict.
    This is the Z3-kernel-checked confirmation that
    R(3) = 6 over GF(2): no 5-multiplication decomposition
    exists.
  - **K=6 SAT** (via `problem.py 3 6` AND `deg2_verify.py`):
    0.1s.  Z3 finds (different) valid 6-mult algorithms;
    `deg2_verify.py` also verifies the hand-coded
    Karatsuba-with-sharing 6-mult.
  - **K=9 SAT**: 0.0s.  Naive 9-mult verifies.

### n=4 (deg-3 × deg-3): R(4) = 9

  - **K=8 UNSAT** (via `problem.py 4 8`): 8.1s with symmetry
    breaking, timeout (>5min) without.  **Z3-kernel-confirmed**
    that no 8-multiplication decomposition exists.  This is
    consistent with Cenk-Hasan 2007's published result.
  - **K=9 SAT** (via `problem.py 4 9`): 7.8s.  Z3 finds a
    valid 9-mult algorithm:

    ```
    m0 = p3 * q3
    m1 = p2 * q2
    m2 = (p2 + p3)(q2 + q3)
    m3 = (p1 + p2)(q1 + q2)
    m4 = (p1 + p2 + p3)(q1 + q2 + q3)
    m5 = p0 * q0
    m6 = (p0 + p2 + p3)(q0 + q2 + q3)
    m7 = (p0 + p1 + p3)(q0 + q1 + q3)
    m8 = (p0 + p1 + p2 + p3)(q0 + q1 + q2 + q3)

    r0 = m5
    r1 = m2 + m4 + m6 + m8         (mod 2)
    r2 = m0 + m1 + m2 + m3 + m7 + m8   (mod 2)
    r3 = m0 + m5 + m6 + m7 + m8    (mod 2)
    r4 = m2 + m3 + m4              (mod 2)
    r5 = m0 + m1 + m2              (mod 2)
    r6 = m0
    ```

    This specific bilinear form ordering may or may not be
    isomorphic to a published one; equivalent under
    affine transformations.

### n=5 (deg-4 × deg-4): pending

Background search in progress (see ~ `/tmp/n5k13.log`).

## (d) NEW RESULTS the synthesizer discovers

> "New" here means: results the synthesizer produces that
> may or may not exactly match published constructions, but
> are independently Z3-kernel-checked.

### Z3-kernel-checked impossibility proofs

The bilinear rank lower bounds for n=3 and n=4 over GF(2)
are now Z3-kernel-checked (modulo the tensor-decomposition
encoding).  Specifically:

  - **R(3) ≥ 6**: Z3 UNSAT at K=5 (0.46s without any
    pruning).  This is an INDEPENDENT verification of
    Cenk-Hasan's lower bound, using a different proof
    technique (SAT-based tensor decomposition vs algebraic
    rank argument).
  - **R(4) ≥ 9**: Z3 UNSAT at K=8 (8.1s with symmetry
    breaking).  Same — independent SAT-based proof.

For most readers, "Z3 says UNSAT" isn't a publishable result
(the math was already known).  But the SAT-based proof
**gives a different witness**: the absence of any
55-Boolean-variable assignment satisfying 45 quadratic
constraints, kernel-checked.  This is in principle
machine-checkable to higher assurance (Lean/Coq export of
the Z3 trace).

### Specific bilinear forms

Each "SAT" verdict produces a SPECIFIC bilinear form
decomposition.  Z3's choices may differ from published
canonical algorithms (which optimize for additional criteria
like minimal addition count).  The decompositions are
catalogued in this report; they're equivalent up to affine
transformations, but the SPECIFIC choices Z3 picks are new
witnesses.

For crypto block sizes (n ≥ 32, GHASH-relevant), even
constant-factor improvements would be practically relevant.
Search at these sizes is gated on more aggressive symmetry
breaking + parallel SAT or specialized tensor solvers
(AlphaTensor-style RL, or §G.5's parametric m_i in our IR).

## (e) NEGATIVE results (things tried that failed)

### n=4 K=8 without symmetry breaking → TIMEOUT

Initially ran K=8 search without lex-ordering symmetry
breaking.  Z3 timed out at 5 minutes (300s).  Adding the
symmetry breaking (lex-order across mults by signature)
collapsed search time to 8.1s.

**Lesson**: for tensor-decomposition SAT problems with
indistinguishable slots, lex-ordering is essential.  The
search space without it is O(K!) larger than with.

### Hand-crafted 5-mult candidates over GF(2) n=3 → all UNSAT

`deg2_discrim_5mult.py` lists 4 hand-crafted 5-mult attempts
(drop m2, drop m1, drop m0c from Karatsuba, alt 5-form
set).  All correctly UNSAT — sanity check that the framework
discriminates at K=5.

This was expected (we now know K=5 is provably impossible),
but the discrim test demonstrates the framework's
discrimination at the BENCHMARK level (not just the direct
SAT search level).

### Earlier "5-mult is open" framing — incorrect

`OPEN_PRBS.md` L2.1b initially framed "whether 5 is
achievable over GF(2)" as an **open question**.  This is
wrong: R(3) = 6 is settled (Cenk-Hasan 2007).  The Z3
UNSAT verdict at K=5 confirms this.

The next genuinely open territory is at LARGER n:
  - n = 5: gap between proven lower bound and published
    upper bound (13).
  - n = 6+: larger gaps.
  - Crypto block sizes: constant-factor improvements.

### n=5 K=13 direct SAT search — wedged

Running `problem.py 5 13` with various timeouts has not
produced a verdict (SAT or UNSAT).  The search space at
n=5 (130 booleans + 225 tensor-equality constraints +
12 lex-ordering pairs) appears beyond what plain Z3 SAT
can decide in reasonable wallclock.  An attempted 25-min
Z3-internal-timeout / 30-min shell-timeout invocation
hung indefinitely past both timeouts and had to be
manually killed at ~53 min wallclock — Z3's internal
timeout apparently didn't fire (possibly because the
parallel-search threads each have their own deadlines
and the harness keeps spawning).

**Lesson**: at this scale, **the direct SAT enumeration
is not the right tool**.  Z3 propagation can rule out
small K quickly (n=4 K=8 in 8.1s), but for K close to
the true rank value the search space dominates.  See
§(g) Exploration for the alternative directions.

A 1-hour background run is in progress (`b1e8det66`) to
gather more data on whether longer wallclock helps.
Expected outcome: timeout without verdict — confirming
that direct enumeration won't scale further.

## (g) Exploration: hybrid Z3-search + Lean axiomatic proving

Asked 2026-05-20: *"in addition to a simple Z3 encoding;
can we leverage our framework with our lean fallbacks to
abstract (e.g., higher sizes or problem subparts) so that
we can look for solutions with a mix of Z3 search and Lean
axiomatic proving?"*

Yes.  Two complementary strategies; both leverage the
existing synth framework's UF + recurrence-axiom path
(already used by `modexp`, `sum_array`, `factorial`).

### Strategy A — Recursive abstraction via UFs

Treat smaller polymul sizes as uninterpreted functions
with correctness axioms.  At each composition level, the
synthesizer counts UF calls as "abstract multiplications"
and Lean discharges the algebraic identities.

```
PROBLEM (polymul_5 via recursive Karatsuba):
  uninterpreted = [
    ("polymul_3", [int×3, int×3], "int×5"),   # known: R(3) = 6
    ("polymul_2", [int×2, int×2], "int×3"),   # known: R(2) = 3
  ]
  axioms = [
    # polymul_3 correctness:
    #   ∀a, b. polymul_3(a,b) = (a₀b₀, (a₀b₁+a₁b₀)%2, ...)
    # Similar for polymul_2.
    # Polynomial identities over GF(2) (distributivity,
    # squaring=identity-on-coeff, etc).
  ]
  atoms[s@B0] = [
    # candidate decompositions (each a specific recipe
    # using K calls to polymul_3 or polymul_2 plus XOR
    # combining):
    _2WAY_KARATSUBA_3_CALLS_TO_POLYMUL_3,
    _TOOM3_5_CALLS_TO_POLYMUL_2,
    _MIXED_5_CALLS,
    ...
  ]
```

**Each polymul_k UF call counts as ONE abstract mult.**
The synth finds a decomposition using K such calls;
Lean verifies the polynomial identity (e.g., "this
Vandermonde inversion at these 5 points correctly
interpolates").

**Decoupled scaling**:
  - **Leaf level** (n ≤ 4): direct Z3 SAT (`problem.py`)
    finds R(k).
  - **Composition level** (n ≥ 5): synth framework + Lean
    axioms verify recursive schemes.

**Worked example for n=5**: recursive Karatsuba 2-way split
gives R(5) ≤ 3·R(3) = 18 (too high).  Cenk-Hasan's
13-mult uses a mixed recipe: 5 polymul_2 calls plus 3
polymul_3 calls or similar — requires a specific
interpolation matrix.  Strategy A would let us VERIFY
each of these decompositions in Lean.

### Strategy B — Template + predicate search over algebraic structure

Treat "evaluate at points → sub-multiply → interpolate" as
a template.  Predicates parameterize the evaluation points
+ interpolation matrix.

```
Template = SB(eval-points) >> SB(sub-multiplies) >> SB(interpolate)
```

Predicate space:
  - **eval-point atoms**: candidate evaluation point sets
    (over GF(2) directly, or over GF(2^k) extension rings).
  - **interpolation matrix atoms**: candidate basis
    transformations.

The PLDI'09 reduction enumerates these.  Each candidate
becomes a concrete K-mult algorithm.  Lean axioms encode
the polynomial identities (e.g., "evaluation at K distinct
points uniquely determines a polynomial of degree < K").

This is the **template-driven** counterpart to bilinear-rank
SAT: instead of enumerating all 16⁵ bilinear forms,
enumerate the much smaller space of "algebraically valid"
interpolation schemes.

### Where each strategy wins

| Regime | Best approach | Why |
| --- | --- | --- |
| n ≤ 4, finding R(n) | Direct Z3 SAT (`problem.py`) | Small Boolean search; Z3 propagates fast |
| n ≥ 5, recursive scheme | Strategy A (UFs + Lean) | Bilinear search wedges; recursion exposes structure |
| Asymptotic n, fixed scheme | Strategy B (template) | Verify a published scheme at arbitrary n |
| Crypto block sizes (n ≥ 32) | Strategy A with careful axioms | Direct search infeasible; recursion is the only path |

### What Strategy A gets us at n=5 specifically

The published R(5) ≤ 13 over GF(2) uses Cenk-Hasan's
"5-way Karatsuba-Ofman-like" decomposition with 13
abstract multiplications.  Strategy A would let us:

  1. Provide `polymul_5` as a UF with the polynomial-product
     axiom.
  2. Provide 13 candidate sub-multiplication recipes as SB
     atoms (each calling polymul_2 or polymul_3 with
     specific input combos).
  3. Provide the interpolation/combining recipe as a
     separate SB.
  4. Lean verifies the algebraic identities — "these 13
     sub-products + this combining = full polymul_5".

The synth then verifies the whole composition.  If
successful: a **Lean-kernel-checked algorithm at n=5
using 13 mults**.

For DISCOVERY (finding 12-mult), we'd need either:
  - Strategy A with a richer predicate space over
    decomposition recipes.
  - Strategy B with §G.5's parametric m_i over the
    interpolation matrices.

### Added value over direct Z3 search

1. **Scales past Z3's wedge points** — n ≥ 5 might be
   tractable via abstraction where direct enumeration
   wedges.
2. **Produces structured proofs** — each composition step
   is a Lean theorem, not a raw SAT model; the proof tree
   is human-readable and ports to Lean files.
3. **Composes with existing benchmarks** — modexp / sum_array
   already use UF + recurrence axioms; the wiring is in
   place via `helper_registry` + the codegen path.
4. **Generalizes to other open problems** — the same
   recursive-UF approach applies to tropical matmul (L2.2),
   addition chains (L2.4), Strassen-3×3 (L1.1 + L2.x at
   crypto sizes).

### Concrete next step (proposal) — ✅ DONE

Prototype Strategy A at n=4 first (where R(4)=9 is known)
as a smoke test:
  - Express recursive 2-way Karatsuba: 3 calls to polymul_2
    + XOR combining.
  - polymul_2 declared as UF; axiom: correctness of deg-1
    polymul.
  - Synth + Lean verifies the n=4 = 3·R(2) composition.
  - Expected: 9 abstract mults match published R(4)=9 (3
    calls × R(2)=3 mults each ≈ 9 scalar mults total).

### Strategy A n=4 prototype — **VERIFIED (2026-05-20)** 🎯

`strategy_a_n4_prototype.py` lands the smoke test.

**Setup**:
  - UF: `polymul_2 : int × int × int × int → int[]` (array-
    valued; coefficients of the degree-2 product).
  - 3 axioms (per output coefficient, universally quantified
    over the 4 input scalars):
    ```
    polymul_2(a0, a1, b0, b1)[0] == a0 * b0
    polymul_2(a0, a1, b0, b1)[1] == (a0 * b1 + a1 * b0) % 2
    polymul_2(a0, a1, b0, b1)[2] == a1 * b1
    ```
  - Recipe: 3 polymul_2 calls + XOR combining (Karatsuba
    2-way split).

**Result**: BOTH candidates verify.
  - Solution #0: naive 9-mult parallel (baseline; score=7).
  - Solution #1: recursive 2-way Karatsuba with 3 polymul_2
    UF calls + XOR combining (score=10).  **The recursive
    scheme is verified via the polymul_2 axioms.**

```python
# Synthesized recipe (Strategy A solution #1):
m0 = polymul_2(a0, a1, b0, b1)
m1 = polymul_2(a2, a3, b2, b3)
m2 = polymul_2((a0+a2)%2, (a1+a3)%2, (b0+b2)%2, (b1+b3)%2)
r0 = m0[0]
r1 = m0[1]
r2 = (m0[2] + m2[0] + m0[0] + m1[0]) % 2
r3 = (m2[1] + m0[1] + m1[1]) % 2
r4 = (m1[0] + m2[2] + m0[2] + m1[2]) % 2
r5 = m1[1]
r6 = m1[2]
```

Total abstract mults: 3 polymul_2 calls (× R(2)=3 scalar
mults each = 9 scalar mults), matching R(4) = 9.

**What this validates**:
  - The synth framework's UF + axiom path handles
    array-valued UFs (`polymul_2` returns `int[]`).
  - Quantified UF-coefficient axioms via ForAll over scalar
    args + Subscript on the UF call output (`polymul_2(...)[k]`).
  - Recursive abstraction VERIFIES at n=4.

**What this enables next**:
  - **n=5 with multiple decomposition recipes**: same UF +
    axioms, recipes using 5 polymul_2 calls + mixed
    polymul_3 calls + interpolation matrix.
  - **n=6, n=7 via 2-way Karatsuba**: 3·R(k) mults, with
    k=3,4 leaves verified separately.
  - **Crypto block sizes (n=32, 64)** via 2-way Karatsuba
    recursion + the eBATS-tracked best-known small-case
    algorithms as Tier-3 helpers.

If the n=4 smoke test works, push to n=5 with multiple
candidate decomposition recipes.  The framework's
helper-citation codegen path is reusable here.

### Strategy A n=5 prototype — **VERIFIED (2026-05-20)** 🎯

`strategy_a_n5_2way_prototype.py` extends Strategy A to n=5
via the unequal 2-way Karatsuba split (n=5 = 3+2).

**Setup**:
  - UFs: `polymul_3 : int×6 → int[]` (5-coef deg-2 × deg-2
    output) AND `polymul_2 : int×4 → int[]` (3-coef deg-1 × deg-1).
  - 5 axioms for polymul_3 (per coefficient) + 3 for polymul_2
    = **8 universally-quantified axioms**.
  - Recipe: 2 polymul_3 calls + 1 polymul_2 call + 4 GF(2)-XOR
    intermediates + 9 output coefficient formulas.

**Result**: BOTH candidates verify.
  - Solution #0: naive 25-mult parallel (baseline; score=9).
  - Solution #1: recursive 2-way 3+2 Karatsuba with 1 polymul_2
    + 2 polymul_3 UF calls + XOR combining (score=16).
    **The recursive scheme is verified via the polymul_2 and
    polymul_3 axioms.**

Total abstract sub-mults: 1 polymul_2 + 2 polymul_3.  At the
scalar level: 1·R(2) + 2·R(3) = 3 + 12 = **15 scalar mults**
(vs 25 naive; vs Cenk-Hasan's 13 published optimum).

**The 15-mult result is suboptimal**.  Cenk-Hasan's R(5) ≤ 13
uses a non-Karatsuba interpolation that 2-way splitting can't
discover.  But the verification of 15-mult recursive Karatsuba
demonstrates Strategy A scales TO n=5; the 13-mult discovery
is gated on a richer predicate space (§G.5 parametric m_i,
or hand-coded Cenk-Hasan recipes as additional candidates).

**Engineering note**: the per-class Z3 timeout (default 10s
in `solver.py:_PER_CHECK_TIMEOUT_MS`) is too short for n=5
quantifier-axiom instantiation work.  The prototype
monkey-patches it to 5 min, which lets Z3 successfully
instantiate the polymul_3 / polymul_2 axioms at the multiple
call sites + combining formulas.  Future cleanup: surface as
a Problem field.

```python
# Synthesized recipe (Strategy A n=5 solution #1):
s_a0 = (a0 + a3) % 2
s_a1 = (a1 + a4) % 2
s_b0 = (b0 + b3) % 2
s_b1 = (b1 + b4) % 2
m_lo = polymul_3(a0, a1, a2, b0, b1, b2)
m_hi = polymul_2(a3, a4, b3, b4)
m_mix = polymul_3(s_a0, s_a1, a2, s_b0, s_b1, b2)
r0 = m_lo[0]
r1 = m_lo[1]
r2 = m_lo[2]
r3 = (m_lo[3] + m_mix[0] + m_lo[0] + m_hi[0]) % 2
r4 = (m_lo[4] + m_mix[1] + m_lo[1] + m_hi[1]) % 2
r5 = (m_mix[2] + m_lo[2] + m_hi[2]) % 2
r6 = (m_mix[3] + m_lo[3] + m_hi[0]) % 2
r7 = (m_mix[4] + m_lo[4] + m_hi[1]) % 2
r8 = m_hi[2]
```

**Diagnostic ladder** (committed alongside; helped find the
per-class timeout issue):
  - `strategy_a_diagnostic.py` — single polymul_3 + read-back.
    Verifies in 6s.  Confirms basic axiom application works.
  - `strategy_a_diagnostic2.py` — two polymul_3 calls (one
    with computed args).  Verifies.  Confirms multi-instance
    + computed-args axiom application works.
  - `strategy_a_diagnostic3.py` — full n=5 Karatsuba with
    GROUND axioms (no quantifiers).  Hit UNKNOWN-reject after
    10s at one class.  Identified the per-class Z3 timeout
    as the bottleneck.

**Next pushes** (still on this experimental branch):
  - **n=5 with mixed Cenk-Hasan-style recipes**: encode the
    13-mult published algorithm as additional candidates,
    verify each via the same UF axiom path.
  - **n=6, n=7 via 2-way Karatsuba**: 3·R(k) recursion;
    leaves use n=3/n=4 small-case recipes.
  - **Crypto block sizes** (n=32 / n=64) via 2-way Karatsuba
    + Tier-3 helpers citing eBATS-tracked best-known small
    cases.

### Hybrid Z3 SAT + UF-abstraction SEARCH (`strategy_hybrid_search.py`)

User feedback (2026-05-20): verifying a hand-coded recipe is
NOT discovery — to leave the possibility of NEW results open,
the synthesizer must SEARCH over the parametric coefficient
space.  Plain Strategy A (Karatsuba 2-way prototype) just
verifies; we need to extend it.

**Hybrid encoding**: parametric L-matrices + γ output
combiners with polymul_k UF oracles.

  - For each call slot k ∈ [1..K] with kind ∈ {p2, p3}:
    L_a^k, L_b^k are arity×n bit-matrices selecting how each
    polymul input is a GF(2)-linear combo of (a_0..a_{n-1}).
  - For each output j: γ_{j,k,c} bits XOR-select which
    polymul_arity coefficients contribute.
  - Universal-over-inputs constraint: tensor-equality over
    GF(2)^n × GF(2)^n.

**Discovery semantics**:
  - **SAT**: a new algorithm with this call-config exists at
    the implied cost.  If cost < published R(n), new upper
    bound.
  - **UNSAT**: the structured decomposition (specifically K
    polymul_k calls + γ combiners) cannot achieve polymul_n.
    Doesn't rule out other structures.
  - **TIMEOUT**: search beyond Z3's budget.

### Hybrid search results (initial sweep)

**n=4 cost 9 (p2,p2,p2): SAT in 17.3s.**  Z3 finds a
**NON-Karatsuba 3-polymul_2-call decomposition** of polymul_4:

```
m0 = p2(a1+a2, a0+a3, b1+b2, b0+b3)
m1 = p2(a0, a1+a3, b0, b1+b3)
m2 = p2(a0+a2, a0+a2+a3, b0+b2, b0+b2+b3)
```

This is structurally DIFFERENT from the standard recursive
2-way Karatsuba (`m_lo=p2(a0,a1,b0,b1)`,
`m_hi=p2(a2,a3,b2,b3)`,
`m_mix=p2(a0+a2,a1+a3,b0+b2,b1+b3)`).  Both achieve cost
9 = R(4).  Demonstrates the framework finds non-isomorphic
optimal-rank decompositions — POPL'10's Strassen lesson at
the polynomial-mult scale.

**Likely not strictly novel** — Cenk-Hasan and follow-ups
have classified the equivalence class of 9-mult algorithms;
Z3's choice is likely related by affine transformation.

**n=3 cost 6 (p2,p2): UNSAT in 0.9s.**  **NEW NEGATIVE
RESULT** (within our framework): there exists NO decomposition
of polymul_3 over GF(2) using exactly 2 polymul_2 calls + γ
combining, even with arbitrary L-matrix linear combinations.

Why this matters: the standard 6-mult Karatsuba-with-sharing
for polymul_3 uses 6 RANK-1 bilinear products (each a single
scalar product of linear combos), NOT 2 polymul_2 sub-blocks.
Z3 confirms that polymul_2-oracle composition is strictly
LESS EXPRESSIVE than 6 free rank-1 products — even at
cost-matched 6 scalar mults.

**Practical implication for L2.1 (n=5 below 13)**: the
hybrid approach restricted to polymul_k oracles is
FUNDAMENTALLY LIMITED.  The optimal decomposition (if one
beats Cenk-Hasan's 13) likely uses raw rank-1 contributions
— which `problem.py` searches but wedges at n=5.

**n=5 cost 15 (p3,p3,p2): TIMEOUT at 4min.**  Even a known-
SAT case (the 2-way Karatsuba scheme our verified prototype
uses) doesn't decide in 4 min via the hybrid encoding.  Z3's
CNF blowup on nested XOR-of-AND-of-XOR constraints (the
polymul_3 coefficient expansion at search time) is the
suspected bottleneck.

### n=4 mixed-config sweep (after p1 addition)

| Config | Cost | Verdict | Time |
| --- | --- | --- | --- |
| (p1×9) | 9 = R(4) | SAT (9 rank-1 products) | 62.7s |
| (p2,p2,p2) | 9 = R(4) | SAT (non-Karatsuba) | 17.3s |
| (p2,p2,p1×3) | 9 = R(4) | SAT | 33s |
| (p3,p1×3) | 9 = R(4) | **TIMEOUT** | 120s |
| (p3,p1,p1) | 8 < R(4) | **TIMEOUT** | 40s |
| (p2,p1×3) | 6 < R(4) | UNSAT | 8.3s |
| (p2,p2) at n=3 | 6 = R(3) | UNSAT (the "new negative") | 0.9s |

**Observation**: high-arity (p3) mixed with low-arity (p1)
is surprisingly HARDER for Z3 than uniform configs.  Even
known-UNSAT cases at cost-8 hit timeout when the config
is (p3,p1,p1).  Suspected: asymmetric L-matrix sizes break
Z3's variable-ordering heuristics; same-kind configs
benefit from lex-ordering symmetry breaking but mixed
configs don't.

### n=5 30-min background sweep (3 configurations, ALL timed out)

After adding p1, three configurations launched as 30-min
background runs.  All three hit timeout without any output:

| Config | Cost | Verdict | Significance |
| --- | --- | --- | --- |
| (p3,p3,p1) | 13 | **TIMEOUT 30min** | At published R(5) |
| (p2,p2,p2,p2) | 12 | **TIMEOUT 30min** | Would beat published if SAT |
| (p1×13) | 13 | **TIMEOUT 30min** | Hybrid encoding of direct SAT K=13 |
| (p3,p3) | 12 | **TIMEOUT 30min** | 2-polymul_3-only attack at cost-12 |

The hybrid encoding at n=5 with cost 12-13 is beyond Z3's
reach in 30 minutes for ANY configuration we tried —
"structured" mixes like (p3,p3,p1), "unstructured" (p1×13),
and the would-be-novel cost-12 attempt (p2×4).

**Practical conclusion**: at n=5, neither direct SAT (problem.py
also wedges at K=13 in 1+ hour) nor hybrid encoding decides
R(5) in budget.  Reaching genuine discovery at n=5 needs:
  (a) Significantly stronger symmetry breaking that
      generalizes across mixed call kinds.
  (b) A different search paradigm (RL like AlphaTensor;
      tensor-decomposition specialized solvers).
  (c) Manual identification of the additional structure
      reducing search to tractable size (e.g., Toom-3 over
      GF(4) extension à la Cenk-Hasan).

The 4-hour direct SAT background (`bivvv5sro`) is still
running.  The (p3,p3) cost-12 background (`bwydlzfl7`) hit
its 30-min timeout without verdict.

### Part A — bottom-up library framework results (2026-05-20)

Per user direction: built a library of verified small-n
decompositions (`library.json`) and a library-aware search
(`library_search.py`) that uses library entries as fixed
sub-blocks.

**Library built (26 entries)**:
| (n, K) | Models | Notes |
| --- | --- | --- |
| (2, 3) | 1 | R(2) optimal — Karatsuba |
| (2, 4) | 3 | Super-optimal (naive 4-mult variants) |
| (3, 6) | 3 | R(3) optimal — Cenk-Hasan-style |
| (3, 7..9) | 3 each | Super-optimal at n=3 |
| (4, 9) | 1 | R(4) optimal — recursive Karatsuba |
| (4, 10..12) | 3 each | Super-optimal at n=4 |

Each library entry is a concrete (L_a, L_b, γ) bilinear-rank
decomposition Z3-kernel-verified.  Built in ~5min total (most
entries under 10s each).

**Library-aware search results**:

| Target | Configuration | Cost | Verdict | Time |
| --- | --- | --- | --- | --- |
| polymul_4 | 3 × polymul_2 K=3 | 9 = R(4) | SAT | 5.1s |
| polymul_4 | 2 × polymul_2 K=3 | 6 < R(4) | UNSAT | 14.4s |
| polymul_5 | 5 × polymul_2 K=3 | 15 > R(5) | SAT | 213s |
| polymul_5 | polymul_4 K=9 + polymul_2 K=4 | 13 | TIMEOUT 15min | — |
| polymul_5 | 2 × polymul_3 K=6 | 12 (below pub) | TIMEOUT 30min | — |
| polymul_5 | polymul_4 K=9 + polymul_2 K=3 | 12 (below pub) | TIMEOUT 30min | — |

**Encoding is sound** (sanity UNSAT at cost < R(n); SAT at
cost ≥ R(n) on small cases).

**At n=5 with cost ≤ 13, the library-aware approach also
wedges** — like direct SAT and hybrid before it.  The 5×polymul_2
SAT (cost 15, 213s) shows Z3 CAN find solutions at this scale
when given enough budget AND when the cost is well above the
rank.  At cost 12-13 (at/below R(5)≈13), Z3 either takes much
longer or genuinely UNSAT — we can't distinguish in 30-min
budgets.

### Pattern across all attempts at n=5 cost 12-13

| Approach | Cost 12 | Cost 13 |
| --- | --- | --- |
| Direct SAT (rank-1) | wedged (1+ hr) | wedged (1+ hr; previously 53min runaway) |
| Hybrid Z3+UF | wedged (30min, multiple configs) | wedged (30min) |
| Library-aware | wedged (30min, 2 configs) | wedged (15min) |

The honest verdict: **R(5) over GF(2) is beyond our framework's
direct reach in 30-min-to-1-hour budgets** regardless of encoding.

### Hybrid lessons banked

1. **Hybrid is for DISCOVERY of STRUCTURED algorithms** —
   "given polymul_k as building blocks, find the recipe".
   Useful when the target is known to use polymul_k oracles
   (e.g., crypto block compositions, recursive schemes).
2. **Hybrid is NOT a free replacement** for direct rank-1
   bilinear-rank search.  For unconstrained optimal-rank
   discovery, direct SAT (`problem.py`) is the right tool —
   but it wedges at n=5.
3. **n=4 (p2,p2,p2) is a sweet spot**: cost-matched
   structured search, fast SAT (17s), produces non-Karatsuba
   instances.  Good demo of the discovery capability.
4. **The next direction to actually push R(5) ≤ 12** needs
   either:
     (a) §G.5 parametric m_i with rank-1 product holes (the
         direct SAT search through the synth framework with
         better symmetry-breaking + propagation).
     (b) Better Z3 encoding (bit-vectors?  Specialized
         tensor-decomposition algorithms outside SAT?).
     (c) Mixed call types in hybrid (add p1 = scalar bilinear
         product as a call kind, allowing the hybrid to
         search rank-1 + rank-3 + rank-5 contributions
         jointly).
     (d) AlphaTensor-style RL search over the discrete
         tensor-decomposition space.

## (h) Final summary

This is the consolidated end-state of the karatsuba_gf2
exploration on the `experimental/open-prbs-karatsuba-gf2`
branch (2026-05-20).

### Verified positive results

| Bench | What | How | Time |
| --- | --- | --- | --- |
| **R(2) = 3** | Karatsuba 3-mult, n=2 deg-1 polymul | Direct Z3 SAT | <0.1s |
| **R(3) = 6** | Cenk-Hasan-style 6-mult, n=3 deg-2 polymul | Direct Z3 SAT | 0.1s |
| **R(4) = 9** | Recursive Karatsuba + Z3-discovered variants | Direct Z3 SAT | 7.8s |

For each, multiple distinct (L_a, L_b, γ) decompositions found
and stored in `library.json` — **26 entries** total spanning
n=2..4.

### Verified negative results (Z3-kernel-checked lower bounds)

| Claim | Proof | Time |
| --- | --- | --- |
| R(2) ≥ 3 | K=2 UNSAT | <0.1s |
| **R(3) ≥ 6** | K=5 UNSAT (even without sym breaking, 0.46s) | 0.0s with sym |
| **R(4) ≥ 9** | K=8 UNSAT | 8.1s |
| polymul_3 NOT decomposable via 2 polymul_2 oracles | hybrid (p2,p2) UNSAT at n=3 | 0.9s |

The R(3) and R(4) lower bounds are independent kernel-checked
confirmations of Cenk-Hasan 2007 via tensor-decomposition SAT.

### Strategy A — recursive abstraction verification

| Bench | Composition | Verified |
| --- | --- | --- |
| polymul_4 via recursive 2-way Karatsuba | 3 × polymul_2 UF calls | ✅ Verified (~10s) |
| polymul_5 via 2-way 3+2 split | 2 × polymul_3 + 1 × polymul_2 UF | ✅ Verified (with bumped per-class timeout) |

Demonstrates the synth framework handles UF + axiom
compositional verification at n=4 and n=5.

### n=4 hybrid sweep (mixed call kinds)

| Config | Cost | Verdict | Time |
| --- | --- | --- | --- |
| (p1×9) | 9 = R(4) | SAT | 62.7s |
| (p2,p2,p2) | 9 = R(4) | SAT (non-Karatsuba algorithm Z3-discovered) | 17.3s |
| (p2,p2,p1,p1,p1) | 9 = R(4) | SAT | 33s |
| (p2,p1,p1,p1) | 6 < R(4) | UNSAT | 8.3s |
| **(p3,p1,p1,p1)** | **9 = R(4)** | **TIMEOUT 120s** | — |
| **(p3,p1,p1)** | **8 < R(4)** | **TIMEOUT 40s** | — |
| **(p3,p3)** | **12 > R(4)** | **TIMEOUT 50s** | — |
| **(p3,p2)** | **9 = R(4)** | **TIMEOUT 2min** | — |

Structural finding: **high-arity (p3) mixed with other kinds
hits Z3 timeouts even at n=4** — asymmetric L-matrix sizes
appear to disrupt Z3's variable-ordering heuristics.

### n=5 wall (across all 3 approaches)

| Approach | Cost 12 (would beat published) | Cost 13 (at published bound) | Cost 15 (above published) |
| --- | --- | --- | --- |
| **Direct SAT** (rank-1) | wedged 1+ hr | wedged 1+ hr (53min runaway) | — |
| **Hybrid Z3 + UF axiom** | TIMEOUT 30min (multiple configs) | TIMEOUT 30min (multiple configs) | TIMEOUT 4min |
| **Library-aware** (fixed sub-blocks) | TIMEOUT 30min (2 configs) | TIMEOUT 15min | **SAT 213s** (5×polymul_2) |

The honest verdict: **R(5) over GF(2) is beyond our framework's
reach in 30-min-to-1-hour budgets, regardless of encoding**.

### Framework conclusions

1. **For n ≤ 4**, our framework Z3-kernel-confirms R(n)
   values matching the literature, finds explicit algorithms,
   and discriminates against sub-optimal candidates.  This is
   the "framework's sweet spot."
2. **For n = 5**, all three encodings (direct rank-1 SAT,
   hybrid UF+axiom, library-aware) wedge at cost 12-13.
   Reaching discovery here likely needs:
     - Substantially stronger symmetry breaking (we couldn't
       find the right form).
     - A different paradigm (RL like AlphaTensor; specialized
       tensor solvers).
     - Manual structural identification (e.g., Toom-3 over
       GF(4) extension à la Cenk-Hasan).
3. **The framework reach is meaningfully smaller than the
   open frontier**.  Even confirming R(5) = 13 (a settled
   result) is out of budget.

### Process / methodology lessons (banked in EXPERIENCE_REPORT CS-11)

- **Direct enumeration isn't the right tool for tensor-rank
  discovery at the framework's edge.**  The wedge IS the
  signal; treat it as evidence for redesigning the search
  shape.
- **Library-aware encoding is sound and Z3-kernel-checked**
  but doesn't fundamentally shrink the search at n=5.
- **Speculation (Part B)** — never exercised in practice;
  the structural argument is that speculation ADDS search
  variables rather than removing them, so it's likely to
  wedge harder at the polymul_5 problem.  Part B's value
  is more in compositional discovery at large N where the
  assumption is genuinely smaller than the conditional
  result.
- **Z3 SIGTERM hides output**: the parallel SAT search
  doesn't checkpoint output, so timeouts leave empty logs.
  Limits introspectability — a real engineering concern
  for any future discovery work.

## (f) References

  - Karatsuba, A.A. and Ofman, Y. (1962). "Multiplication of
    Many-Digital Numbers by Automatic Computers."
  - Toom, A.L. (1963). "The complexity of a scheme of
    functional elements realizing the multiplication of
    integers."
  - Strassen, V. (1973). "Vermeidung von Divisionen."
    J. Reine Angew. Math. 264, 184-202.  Lower bound 2n−1.
  - Hopcroft, J.E. and Kerr, L.R. (1971). "On minimizing
    the number of multiplications necessary for matrix
    multiplication."
  - Montgomery, P.L. (2005). "Five, six, and seven-term
    Karatsuba-like formulae."  IEEE Trans. Comput. 54(3),
    362-369.
  - Cenk, M. and Hasan, M.A. (2007). "On the arithmetic
    complexity of Strassen-like matrix multiplications."
  - Cenk, M. and Hasan, M.A. (2009). "On the multiplication
    of finite fields, polynomials over GF(2): improvements
    over Mastrovito's algorithm."
  - Bernstein, D.J. (2009). "Batch binary Edwards."
    CRYPTO '09.  Hand-optimized small-case GF(2) polymul.
  - Cenk, M., Hasan, M.A., Negre, C. (2009). "Improved
    three-way split formulas for binary polynomial
    multiplication."  CHES '09.
  - eBATS benchmark suite (D.J. Bernstein): tracks best-known
    multiplication counts at crypto block sizes.

## Files

| File | Purpose |
| --- | --- |
| `problem.py` | Parametric Z3 SAT search.  Usage: `python problem.py N K [timeout_s]`.  Encodes the tensor decomposition for degree-(N−1) polymul over GF(2)[x] with K bilinear products. |
| `deg1_verify.py` | n=2 smoke test: verify 3-mult Karatsuba and 4-mult naive. |
| `deg1_discrim_2mult.py` | n=2 discrim: 4 hand-crafted 2-mult candidates all UNSAT. |
| `deg2_verify.py` | n=3 verification: 6-mult Karatsuba-with-sharing and 9-mult naive. |
| `deg2_discrim_5mult.py` | n=3 discrim: 4 hand-crafted 5-mult candidates all UNSAT. |
| `deg2_search5.py` | n=3 direct Z3 SAT search for K=5 (now subsumed by `problem.py`). |
| `REPORT.md` | This file. |
