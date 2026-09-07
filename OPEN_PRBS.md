# Open benchmark candidates

Catalog of candidate benchmarks whose published "best known"
algorithm has an open gap below it — either the optimal
mult-count, comparison-count, or asymptotic complexity is
genuinely unresolved.  Successful synthesis of one of these
would be a real result, not just a verification.  North star
#3 ("discover programs that haven't been invented yet"; see
`RESEARCH.md §G`).

**Why this catalog exists.**  Toom-3, Karatsuba, Strassen-3×3
(Laderman-23), and Bresenham all VERIFY in our corpus.  But
each has a known optimum (or a published best).  The next leap
is benchmarks where the optimum is OPEN — where synthesis
could plausibly surface a new realization.  POPL'10's 2×2
Strassen template already produced unpublished 7-mult variants;
the discrim test `strassen_3x3_lt23mult_search` (23 hand-crafted
22-mult candidates, all correctly UNSAT) confirmed our
framework's discrimination but exposed that real discovery
needs the parametric m_i extension banked in `RESEARCH.md §G.5`.

**Effort sketch.**  Variable per candidate.  Some need §G.5's
parametric m_i template (multi-week IR extension).  Others
(GF(2^k) variants, addition chains) slot directly into the
current IR with new UF axioms.

**Promotion**: items mature here, then become benchmark files
under `benchmarks/open_prbs/` (with paired discrim tests when
applicable).  See `RESEARCH.md` for the broader research
framing.

---

## Layer 1 — Concrete open problems with minimal IR extension

Each is matched to the current IR with at most modest extension.
Verifying the published algorithm is the warmup; the discrim
test (sub-optimum candidates rejected) is the discovery target.

### L1.1 — 3×3 Boolean matrix multiplication below 27 ANDs

The AND/OR semiring has no subtraction, so Strassen-style
cancellation doesn't apply.  The bilinear AND-count for 3×3
Boolean matmul is genuinely unknown — naive is 27, no proof of
optimality.  `boolean_matmul_3x3.py` already exists as the
naive verification; the gap candidate would be a discrim test
mirroring `strassen_3x3_lt23mult_search`.  Framework gap:
parametric m_i with coefficient holes from `{0, 1}` (Boolean)
instead of `{-1, 0, 1}` (integer).

### L1.2 — Hopcroft-Kerr 2×3 × 3×2 below 11 mults

Multiplying a 2×3 matrix by a 3×2 matrix yields a 2×2 result.
Hopcroft-Kerr 1971 showed 11 mults suffice over ℤ; whether 10
is achievable over ℤ is **open**.  Smaller search space than
3×3 (~12 bilinear products instead of 23); lower bound is
closer.  Concrete benchmark: verify the 11-mult algorithm,
then discrim-test 10-mult candidates.

### L1.3 — Tropical (min-plus) 2×2 matmul below Strassen-7

For 2×2 matrix product under min-plus arithmetic (used in
shortest-path acceleration), Strassen-7 doesn't apply because
the algebraic structure lacks subtraction.  Optimal bilinear
count under min-plus is **open** even at 2×2 scale.  Practical
applications in tropical-Floyd-Warshall.  Framework: UF axioms
for min and plus; bilinear search with non-ring structure.

### L1.4 — Toom-4 with optimal integer interpolation points

Degree-3 polynomial multiplication needs 7 multiplications
(Toom-4 over ℤ).  The standard interpolation point set
`{0, ±1, ±2, 3, ∞}` produces sub-optimal intermediate
coefficient growth.  **Open**: is there a better integer point
set?  Same IR shape as `toom3_deg2.py`; just more atoms.

### L1.5 — Karstadt-Schwartz 2017 fewer-additions Strassen

Karstadt-Schwartz found that the 2×2 Strassen variant
`{1,12,12,8,8,7,12}` uses 12 additions instead of Strassen's 15
(while still using 7 mults).  Whether even fewer additions are
achievable for a 7-mult 2×2 product is **open**.  Direct
extension of our existing Strassen-2×2 benchmark; just need to
track addition counts as a cost criterion.

### L1.6 — Bipartite matching with augmenting paths

Hopcroft-Karp achieves O(E·√V) for bipartite matching.  For
restricted graph classes (e.g., interval graphs, bipartite
permutation graphs), the optimal complexity is **open**.  The
algorithm's correctness involves a matching invariant + an
augmenting-path predicate; our quantified-atom + UF framework
handles this naturally.

**Status (2026-05-23): concrete-ops substrate landed, open
question still open.**
COST_INVS §§1–4 (`COST_INVS.md`) landed the cost-invariants IR
extension + Lean substrate
(`SynthLean.Graph`, `SynthLean.Matching` —
HopcroftKarpCost / GloverIntervalCost / BucketedIntervalCost
axioms).  The §4 speculation framework
(`benchmarks/open_prbs/l16_bipartite_matching/speculate.py`)
sweeps (template, cost-target) pairs over the three named
algorithms × {LOOSE, LINEAR, TIGHT_OPEN}: 2 self-matching valid,
6 cross-pair invalid, **TGT_TIGHT (sub-N+E) INVALID for ALL
templates** in our enumerated library.  Trivial lower-bound
axioms (output-size + edge-list-read + endpoint-read) confirm
TGT_TIGHT can't be reached by these templates.

Slice A (`bench_glover_explore.py`, 2026-05-22) demonstrated
multi-candidate algorithm-step exploration via UF axioms.  Slice
B (2026-05-23) replaced the UFs with concrete operations across
four sub-benchmarks: `bench_pair_consecutive` (first E2E
concrete matching), `bench_pair_multi_count` (multi-candidate
exploration discriminated by a count invariant + concrete IR
operations), `bench_glover_concrete` (Slice A → Slice B
unification — concrete pool + cost-bound).  COST_INVS §5 marks
the cost-bound infrastructure validated on concrete state.
emit_py / emit_c / emit_rust extended for `int[][]` (Slice
B.3), so synthesized matching solutions compile to real source.

Slice C (`bench_l16_multi_template.py`, 2026-05-23) lands
multi-VARIANT exploration at the TEMPLATE level via the
`synth.multi_template` parallel-subprocess harness
(RESEARCH.md §I).  Three algorithm shapes for the same
clique-graph matching spec: T_A linear sweep (PICK, 316s,
score 29.50), T_B two-pointer (PICK, 652s, score 37.50),
T_C no-op (REJECT, 0s).  Total wall 969s sequential mode.
Closes the algorithm-exploration tripod: candidates / concrete
ops / shapes — same spec, three different algorithms, framework
correctly distinguishes valid from invalid.

**What still blocks the L1.6 open question**: B.1–B.4
benchmarks are restricted to **chain graphs**
(`G[k][k+1] >= 1` precondition) with a count-bounded post in
place of true maximum-matching.  Real L1.6 attack (sub-O(N + E)
on arbitrary bipartite graphs) needs an inner partner-search
loop, augmenting-path detection, and an augmenting-path-free
invariant.  Multi-week framework extension; banked.  The open
question survives as a characterized gap, not just folklore.

---

## Layer 2 — Speculative + framework-matched

More open-ended; matched to our IR but might need exploration
to land cleanly.  Several are "outside the box" beyond
matrix/polynomial multiplication.

### L2.1 — Karatsuba over GF(2^k) below ⌈n·n^{log₂3 - 1}⌉

**State of the art.**  Karatsuba over GF(2)[x] at degree 1
uses 3 mults; n×n via recursion gives n^{log₂3}.  Schönhage
1977 gives O(n log n log log n) via FFT analogues.
Bernstein 2009 has extensively optimized small cases for
crypto block sizes (AES-GCM, GHASH, post-quantum schemes);
eBATS tracks the best-known counts.

**Genuinely open at small scale:**
  - **n=3** poly mult over GF(2): currently 6 mults via
    Karatsuba-style — whether 5 is achievable is **open**.
  - **n=4**: ~9 mults — similar open lower bounds.
  - **Cryptographic block sizes** (64×64, 128×128 over
    GF(2)): intensively studied, current best ~5-15% above
    conjectured lower bounds.
  - **Toom-style over GF(2^k)** with optimal extension-field
    evaluation point selection — open at most non-trivial
    degrees.

**Framework match: HIGH.**  GF(2^k) is just a UF (`gf2_mul`)
with characteristic-2 axioms (distributivity,
`(a + b)² = a² + b²`).  Same shape as `karatsuba_deg2.py`,
swap ℤ for GF(2).  Bilinear-rank search uses coefficient
holes from `{0, 1}` — STRICTLY SMALLER than the integer case
({-1, 0, 1}).  §G.5's parametric m_i extension applies
directly.

**Concrete tractable sub-problems:**
  - **L2.1a** (~1 week): verify Karatsuba-3-mult over
    GF(2)[x] deg 1.  Smoke test.
  - **L2.1b** (~2-3 weeks with §G.5 extension): discrim-test
    5-mult candidates for GF(2) n=3.  Finite candidate space,
    open lower bound at 6.
  - **L2.1c** (multi-week): search 32×32 GF(2) mul below
    current best.  Crypto-relevant.

**Risks.**  Small-instance lower bounds may already be
proven in the algebraic-complexity literature (need a real
literature review before claiming open).  Crypto-block-size
searches grow exponentially.

**Verdict.** **Strongest framework match of any Layer 2
candidate.**  Promote to top tier alongside L2.2.

### L2.2 — Sub-cubic min-plus matrix multiplication

Williams 2014's algorithm is the canonical near-cubic min-plus
matmul.  Truly sub-cubic min-plus matmul over ℤ is **wide
open**.  Even small instances (e.g., 4×4 in fewer than 64
operations) would be interesting.  Same framework as L1.3 but
larger scale.  This is the APSP-subcubic open problem in
concrete form.

### L2.3 — Triangle detection in restricted graph classes

Alon-Yuster-Zwick O(n^{2.79}) via matrix mul is the dense-graph
best.  For SPARSE graphs (m edges), Bjorklund-Pagh-Williams give
O(m^{1.41}); the precise lower bound is **open**.  Framework:
adjacency-matrix UF axioms + nested-loop template; subset count
is the proof obligation.

### L2.4 — Optimal addition chains for specific exponents

Standard modexp uses ~2·log₂(e) mults.  For specific exponents
(e.g., e ∈ {15, 23, 27, 31}), shorter **addition chains** are
known but not always optimal.  Optimal chain length tabulated
for e ≤ 100; gaps remain for larger exponents.  Modest
extension to our existing `modular_exponentiation` benchmark —
turn the exponent decomposition into a search space.

### L2.5 — Sub-quadratic LCS for restricted alphabets

Longest Common Subsequence is O(nm) classical.  **The
unrestricted version is SETH-blocked**: Backurs-Indyk 2015
showed an O((nm)^{1-ε}) algorithm would refute SETH.  So the
"sub-quadratic LCS" headline is essentially closed under
standard complexity assumptions.

What remains genuinely **open** is the RESTRICTED-alphabet
case (e.g., binary or constant-sized alphabets) — some
sub-quadratic algorithms exist (Bille-Farach-Colton 2008,
Grabowski 2016) but the optimal complexity for fixed
alphabet is unresolved.  Framework match: same as
edit_distance with an alphabet-constraint UF axiom.

**Caveat**: the synthesis search space here is in
algorithm-templates that depend on alphabet structure
(bit-parallelism, automaton-encoded matches) — closer to
"verify a known algorithm" than "discover a new one."

### L2.6 — Subset sum: deterministic / restricted-distribution variants

The headline "O(n·W^{0.99}) unconditionally" claim is
**effectively closed**: Bringmann 2017 already gives
randomized O((n+t)·polylog) via FFT-style convolution, AND
Cygan-Mucha-Wegrzycki-Wlodarczyk 2017 proved a
SETH-conditional lower bound ruling out O((n+t)^{1-ε}).

What remains genuinely **open** is narrower:
  - **Deterministic** O((n+t)·polylog) algorithms (Bringmann
    is randomized).
  - Sub-quadratic algorithms for SPECIFIC value distributions
    (small integers, sparse value sets, geometric).
  - Better approximation factors for the FPTAS variants.

Framework match: DP template with UF recurrence; ranking on
subset cardinality.  **Honest scope**: this is polish on
known algorithms, not novel-program discovery — the
synthesizer can verify Bringmann or derive deterministic
variants, but the algorithm-template space is well-mapped.

### L2.7 — Sub-cubic CYK context-free parsing

Cocke-Younger-Kasami parsing is O(n³); Valiant 1975 reduced it
to Boolean matrix multiplication, giving sub-cubic theoretical
complexity.  Whether truly sub-cubic CYK is practical is
**open** — large constants in Valiant's reduction.  Framework
handles DP-shaped algorithms naturally; the reduction itself
would be a complex template chain.

### L2.8 — Tropical eigenvalue / cycle-mean computation

**State of the art.**  Karp 1978 gives O(VE) minimum cycle
mean — the classical reference, essentially optimal.
Young-Tarjan-Orlin 1991 refined.  Howard's algorithm (1960):
O(VE · iterations), empirically faster than Karp; iteration
bound is open.  Dasdan 2004 surveys experimentally.

**Genuinely open:**
  - Whether O(V^ω) or O(V·E^{1-ε}) is achievable on **dense
    graphs** — open ~40 years, no recent breakthroughs.
  - **Howard's iteration count**: empirically small,
    theoretically Ω(V·E); tight bound open.
  - **Online / incremental** versions when edges added/removed.

**Framework match: MEDIUM.**  Adjacency-matrix UF + tropical
(max/min, plus) operations are fine.  BUT the natural proof
obligation here is **convergence** — "iterative scheme
reaches the eigenvalue in O(f(V,E)) rounds" — which our
framework doesn't natively express.  Our path is partial-
correctness + termination, not convergence-rate bounds.

**Concrete sub-problems:**
  - **L2.8a**: verify Karp's correctness (cycle mean equals
    iterative-improvement fixed point).  Tractable.
  - **L2.8b**: verify Howard's correctness.  Harder
    (invariant tracks current policy + cycle structure).
  - **L2.8c**: search for sub-quadratic dense cycle-mean
    algorithm.  **Multi-decade open; very unlikely from
    synthesis.**

**Risks.**  State of the art stable since 1990s — community
has tried, synthesis unlikely to outpace.  Convergence rate
isn't a natural fit; would require extending obligation
system.

**Verdict.**  Best as a "framework-reach demonstration"
(validates UF axioms for tropical algebra) rather than a
novel-discovery target.  Demote to weaker tier.

### L2.9 — k-shortest simple paths

**State of the art.**  Yen 1971: O(k·V·(E + V log V)) for
k-shortest SIMPLE paths in directed graphs — the classical
reference.  Lawler 1972 independently derived.  Eppstein 1997:
O(m + n log n + k) for k-shortest paths (NOT simple; paths
may repeat vertices) — massive practical advantage.
Hershberger-Maxel-Suri 2007: improved bounds for some
variants.

**Genuinely open:**
  - **Sub-quadratic in k for SIMPLE paths on dense graphs** —
    Yen's hasn't been beaten asymptotically since 1971.
  - Sparse-graph improvements for simple-path variant —
    partial results, lower bound open.

**The difficulty**: the "simple path" constraint requires
**reasoning about visited-vertex sets** ("no vertex appears
twice on a path") — set-membership reasoning that our
quantified-atom framework doesn't handle elegantly.

**Framework match: LOW-MEDIUM.**  Graph adjacency UF and
Dijkstra-style innermost loops are fine, but the
path-uniqueness constraint needs a UF like `visited(path_id,
vertex)` with axioms over insertion, and Yen's outer "deviation
vertex" enumeration has subtle ranking-decrease reasoning.
Priority queues / Fibonacci heaps: data-structure inventions
our search can't naturally surface.

**Concrete sub-problems:**
  - **L2.9a**: verify single-source Dijkstra.  Already
    tractable shape; our floyd_warshall covers all-pairs.
  - **L2.9b**: verify Yen's for k=2 — "second shortest
    simple path."  Requires path-uniqueness UF design.
  - **L2.9c**: search for sub-quadratic-in-k algorithm.
    **Multi-decade open; very unlikely from synthesis.**

**Risks.**  Path-uniqueness invariants don't fit our atom
shapes naturally.  State-of-the-art improvements (Eppstein's
"path graph" technique) are data-structure inventions, not
algorithm-template moves.

**Verdict.**  Weakest framework match of the three deeper-
assessed candidates.  Realistically a "verify Yen's
correctness" target; novel discovery very speculative.

### L2.10 — Optimal Steiner tree on small instances

Dreyfus-Wagner is O(3^k · n + 2^k · n²) for k terminals.
Sub-exponential in k is **open**.  Framework handles small-k
DP; the predicate space gets large fast.

### L2.11 — Reed-Solomon decoding with combinatorial improvements

Berlekamp-Massey decoding is O(n²) for n syndromes.  The
**bounded-distance** decoder is fully understood, but
list-decoding (Guruswami-Sudan, Koetter-Vardy) has open
constants and best-known thresholds aren't proven tight.

**Honest scope**: niche — most open questions are about
constants and field-arithmetic micro-optimizations, not
novel algorithm shapes.  Synthesis can verify Berlekamp-
Massey from UF axioms; whether it would surface a
genuinely-novel optimization is uncertain.  Keep as a
"if we land L2.1 (GF(2^k) Karatsuba) it falls out" follow-on
rather than a primary target.

---

## Honest ranking (Layer 2 after the honesty pass)

**Strongest (framework can plausibly contribute novel result)**:
  - **L2.1** — Karatsuba over GF(2^k) — **promoted to top tier**
    after deeper assessment.  Small-instance open (n=3 below
    6 mults), perfect framework match, crypto-relevant payoff.
  - **L2.2** — Sub-cubic min-plus matmul (small n)
  - **L2.4** — Optimal addition chains for specific exponents

**Middle tier (framework match but harder open questions)**:
  - **L2.3** — Triangle detection in sparse graphs
  - **L2.7** — Sub-cubic CYK parsing
  - **L2.10** — Optimal Steiner tree on small instances

**Weaker / framework-reach demonstrations (open in narrow
sense; novel discovery unlikely)**:
  - **L2.5** — Sub-quadratic LCS (only restricted-alphabet open)
  - **L2.6** — Subset sum (polish on Bringmann)
  - **L2.8** — Tropical eigenvalue — **demoted from middle tier**
    after deeper assessment.  State of the art stable since
    1990s; convergence-rate proofs not natural for our
    framework.  Best as "verify Karp's algorithm" demo.
  - **L2.9** — k-shortest simple paths — path-uniqueness
    constraint doesn't fit atom shapes naturally; data-
    structure-bound improvements.
  - **L2.11** — Reed-Solomon decoding

Top pick if forced to one: **L2.2** (sub-cubic min-plus matmul
at 4×4 or 5×5) — connects to a famous open problem (subcubic
APSP), builds on existing FW + Boolean matmul infrastructure,
and shares the framework gap with L1.1 so the IR-extension
work composes.

**L2.1 (Karatsuba over GF(2^k))** is now the second-strongest
contender after deeper assessment.  Crypto-block-size
optimization has practical payoff even on partial progress;
small-instance lower bounds need a lit review before
committing.

---

## Layer 3 — IR-extension family: straight-line-program with slots

Some open problems share a common shape that our current IR
doesn't natively express: a **fixed-length straight-line program
where each step is one primitive operation chosen from a finite
alphabet, and the search is over the choice at each slot**.  Once
the primitive-op alphabet is parameterized, a single IR extension
unlocks an entire family of combinatorial-search problems.

### L3.0 — The IR design (foundational; landed via L3.1)

A new template node `Network([Slot(), ..., Slot()])` (or similar
name).  Each `Slot()` ranges over a finite list of primitive
operations.  Constraint generation simulates the network on a
finite set of "test inputs" (typically all of `{0, 1}^n` for
small n) and asserts the output matches the spec.

Why this fits the framework's strengths:
  - **Search dim**: |slots| × log₂(|prim-ops|) booleans — typically
    100-300, within our verified sweet spot.
  - **Correctness checker**: finite-input simulation, encoded as
    Z3 propagation constraints across slot outputs.
  - **L1.2-pattern speculation**: fix some slots to known-good
    sequences (a sub-network as library entry) + search residual.

The first concrete target is **sorting networks at n=10 below 31
comparators**.  Each `Slot()` picks a `CompareExchange(i, j)` over
n wires.  Correctness check via the **zero-one principle**: a
comparator network sorts every input iff it sorts every 0/1
input.  Lit reference: Codish-Cruz-Filipe 2014 (SAT-based
synthesis closed n=9 at 25 comparators).

### L3.1 — Sorting networks (concrete first target)

**State of the art.**  Optimal comparator counts known exactly
for n ≤ 9 (Codish et al. 2014 closed n=9 at 25).  n=10 has a
SAT-based lower bound around 29 and a construction at 31;
the gap is genuinely open.  n=11, n=12 wider gaps.

**Framework match**: high once L3.0 lands.  Search dim for n=10,
c=29 is ~174 booleans plus 2¹⁰ × 29 ≈ 30K propagation constraints.

### What the L3.0 IR extension unlocks (follow-on family)

Once the SLP-with-slots IR is in, each of the following slot-op
alphabets gives a new problem family at minimal extra cost:

  - **L3.1** — Sorting networks (slot = compare-exchange).  Open
    at n=10, n=11, n=12.
  - **L3.2** — Selection networks (slot = compare-exchange,
    spec = k-th order statistic).  Optimal sizes open for many
    (n, k) pairs.
  - **L3.3** — Merging networks (slot = compare-exchange, spec
    = merge two sorted sequences).  Knuth's odd-even merge
    optimal for some n only; smaller n have open gaps.
  - **L3.4** — Branchless code synthesis (slot = arithmetic /
    bitwise ops; spec = `abs`, `sign`, `min`, conditional select,
    parity).  *Hacker's Delight*-style; minimum op count
    often unproven.
  - **L3.5** — Bit-manipulation tricks (slot = shift / xor / and /
    or; spec = popcount, bit-reverse, Hamming-weight encoding).
    Optimum op count for many specific bit-twiddling kernels
    open.
  - **L3.6** — Constant-time crypto primitives (slot = same as
    L3.4; spec = data-independent comparison, conditional move,
    blinded select).  Practical payoff: cache-/timing-attack-
    resistant crypto primitives.
  - **L3.7** — Reversible / Toffoli networks (slot = Toffoli /
    CNOT / NOT; spec = bijective permutation of n bits).
    Connects to quantum-circuit synthesis.
  - **L3.8** — SLP with binary + and × together (slot = ±add
    OR × of two earlier wires; spec = bilinear-rank
    decomposition with shared sub-expressions).  This is the
    **retrofit for L1.5 K-S 12-add attack**: our current
    `encoding_joint.py` is an ad-hoc joint encoder that wedges;
    a clean SLP-with-multiplications IR would handle the bilinear
    + SLP joint problem natively and would also be the right
    substrate for AlphaTensor-style matmul-rank discovery.

The natural cadence: land L3.0 + L3.1 together (one IR extension,
one concrete benchmark).  Then L3.2-L3.7 each take days, not
weeks, since they reuse the IR.  L3.8 is the highest-payoff
follow-on because it lets us re-attack L1.5 (K-S 12 adds) and
opens a generalized search for bilinear-rank decompositions
(connects back to L1.2 / L1.5 / L2.1 / L2.2).
