# RESEARCH.md

Forward-looking research threads for the synthesizer.  When the
foundations (Phase 5+) are solid on real-world examples, these are
the next pursuits.  `DESIGN.md` keeps a one-paragraph pointer to this
file; `README.md` summarizes for public visibility.  This file is
the canonical home for the detailed pitches, open questions, and
sub-thread expansions.

This file is updated when a research thread evolves (a sub-thread
splits off, an open question gets resolved, a new direction
surfaces), not on every implementation phase.  See `CLAUDE.md`'s
"Phase-completion routine" for the upkeep workflow.

## North stars

Three long-horizon dimensions that all research threads here
point toward (full statement in `README.md` / `DESIGN.md §0`):

1. **Resource-bounded synthesis.**  Today: correctness +
   termination from English.  Target: `(code, proof_correctness,
   proof_runtime, proof_space)` — worst-case time + space bounds
   per PLDI'09-style resource templates layered on the same IR.
2. **Module-level synthesis.**  Today: one function per
   `Problem`.  Target: full programs with synthesized interfaces
   between submodules, verified via assume-guarantee.
3. **Discovering novel programs.**  POPL'10's Strassen template
   produced unpublished 7-multiplication realizations.  Long-
   horizon goal: given English + resource upper bounds, synthesize
   programs that may be new to the literature.

§A (LLM front-end) and §B (Lean backend) are the **enabling
infrastructure** for these north stars; §D (Phase X+Y) is the
**bridge** that builds the corpus and driver-LLM.  Resource and
module dimensions become **§E / §F** (to-write) once the bridge
phases stabilize.

---

## §A. Natural-language front-end via a small LLM

> **Phase plan note (2026-05-16).**  This thread is now Phase Y.1
> in the unified roadmap (§D below).  The same driver-LLM that
> handles English → `Problem` also handles per-instance Lean
> proof sketches (§B / Phase Y.2).  Read §D first for the
> sequencing.

> **Implementation-detail pointer (2026-06-07).**  Detailed
> FT plan (data generation, base-model selection, framework,
> where to FT, cost estimates, phase plan) lives in
> [`NL_FRONTEND.md`](./NL_FRONTEND.md) — the parked design
> doc.  §A here remains the conceptual framing; embark via
> NL_FRONTEND.md when ready.

**Goal.** Use an 8B–32B class LLM as the *proposer* in the
synthesis loop: take an English program specification and produce
a `Problem` object that the synthesizer solves.

### A.1 Why this is the right shape

- The synthesizer is sound — it verifies code against the spec
  via Z3 (or eventually Lean; see §B).  It never accepts an
  unsound proposal.
- The LLM is untrusted.  It hallucinates atoms, picks bad
  templates, mis-specifies posts.  The synthesizer catches these
  and pushes back via structured failure channels.
- A small LLM is enough when the verification layer carries the
  correctness burden.  The LLM doesn't have to reason about proof
  validity; it only has to *propose plausibly*.  That's exactly
  the regime where 8B–32B models are cost-effective and iterable.

**The skill files (`problem.skill`, `debug.skill`) are
specifically designed for this loop.**  They distill the
recommendations and debugging patterns into LLM-loadable context.
A driver model that reads them as system context, then iterates on
the English spec → `Problem` translation, gets all the
hard-earned knowledge of what works and what doesn't.

### A.2 Iteration loop sketch

```
input:  english_spec
output: (code, proof)  OR  (irrecoverable_failure, diagnostic)

while attempts < budget:
    problem = LLM.propose(english_spec,
                          context=[problem.skill, debug.skill],
                          prior_failures=failures)
    result  = synth.solve(problem)
    match result:
        SolveResult(solutions): return emit_c(best, problem), proof
        NoSolution(hints):      failures.append(("unsat", hints))
        Timeout(hole_sizes):    failures.append(("timeout", hole_sizes))
```

The LLM only needs to be good at:

- Choosing a control-flow template from the natural-language hint.
- Authoring a useful predicate space (atoms drawn from the spec's
  vocabulary).
- Reading structured failures and refining the proposal.

**Validation idea.** A "spec → tested binary" pipeline: the LLM
iterates until the synthesizer succeeds AND the emitted C passes a
battery of sample inputs derived from the Pre.  Failure modes (LLM
never converges, infinite iteration, hallucinated atom that the
synthesizer accepts but is wrong) become explicit signals, each
correctable in the LLM prompt without changing the synthesizer.

### A.3 Open questions

- Which 8B/32B model produces useful first-shot proposals on
  `problem.skill`?  Llama, Qwen, Mistral — empirical.
- How many iterations before convergence on a typical benchmark?
  Budget the wall-clock.
- Does the `debug.skill` content actually help the LLM diagnose
  its own failures, or does it need a different presentation
  (e.g., shorter, more example-driven)?

---

## §B. Lean-based proof alternative

> **Phase plan note (2026-05-16).**  Ring 1 + Ring 2 of this
> thread are landed (Lean integrated as a sound-by-default
> verifier with UNKNOWN fallthrough; see `RESEARCH.LEAN.md` §Ring 1
> and `SOUNDNESS.md`).  Next step is **§D Phase Y.2**: the
> driver-LLM constructs per-instance proof sketches for
> obligations Lean's generic tactic chain can't auto-discharge.
> We are explicitly NOT investing in per-shape auto-tactic
> templates — that's a brittle approach that doesn't scale to
> the long tail.

**Goal.** Add a second proof backend — Lean 4 with tactic-based
proof construction — as an alternative to the SMT path.

> **Status update (2026-05-14):** Lean is now being considered as
> the proof backend for compressor / encoder benchmarks
> (run-length, Base64, LZ77/LZW, vector rotate) that were
> originally scoped to PINS in `DESIGN.md` Phase 4.  PINS is on hold
> pending empirical evidence that Lean's structural-induction
> tactics can dispatch path-coverage-style obligations more
> naturally than PLDI'11's symbolic-executor + safepath approach.
> If the Lean path generalizes well, Phase 4 PINS is dropped
> entirely; otherwise PINS comes back.  This is now a real fork in
> the road, not just a parallel research thread.

### B.1 Motivation

The current PLDI'09 reduction encodes proof obligations as
quantifier-free SMT queries and enumerates atom subsets.  This is
great for predicate-abstraction-shaped problems but hits walls
when:

- The proof requires structural induction over a recursive data
  shape (lists, trees, ASTs).
- The atom space needed for SMT to discharge a quantified
  obligation is huge, but a few well-chosen tactics in Lean
  would dispatch it directly.
- The spec is dependently typed or involves higher-order
  reasoning that SMT can't express natively.

Lean 4 has a mature tactic system (`induction`, `omega`, `simp`,
`exact`, `rewrite`, custom combinators) that handles these
classes well.

### B.2 Sketch

```
problem ─[translate]→ Lean 4 proof obligation
                  └─[LLM proposes tactics]→ Lean check
                                              ├─ success → done
                                              └─ failure → LLM refines
                                                            tactics
```

The LLM's role is heavier than in the SMT path.  Each tactic
proposal is a *step* in proof search, not a one-shot proposal.
The LLM needs to:

- Understand which tactics apply at each goal state.
- Anticipate which lemmas it will need from `Mathlib`.
- Decompose hard goals into smaller intermediate `have` lemmas.

This is firmly in "LLM as proof-search heuristic" territory —
established research direction (Lean Copilot, LeanDojo, etc.).
What's novel for this project is the *integration*: same `Problem`
API, two proof backends, automatic dispatch (try SMT first, fall
back to Lean for goals it can't handle).

**Why the two backends complement each other.**  SMT is fast but
limited in expressivity.  Lean is expressive but slower (per-tactic
LLM calls).  The hybrid lets each handle its strengths:

- Pure predicate-abstraction goals → SMT, milliseconds-to-seconds.
- Inductive / structural goals → Lean, seconds-to-minutes per
  iteration but with stronger guarantees.

### B.3 Open questions

- Translation overhead: `Problem` → Lean obligation.  Trivial
  Pre/Post become Lean propositions; quantified atoms become `∀`
  binders.  The harder piece is the *template* — does the
  flowgraph map naturally onto Lean's program logic, or do we need
  a custom Hoare-style embedding?
- LLM tactic proposal granularity: one tactic at a time
  (responsive, expensive) or batches of conjectured tactics (lower
  call count, more retries)?
- When does the SMT path fail in a way that signals "fall back to
  Lean"?  Need a heuristic; pure UNSAT isn't necessarily a
  Lean-suitable failure.

### B.3.5 Strengthening abstract Loop transitions (precision limit)

**Phase Tier-1 push finding (2026-05-19, Lesson #55).**  Even
with all the soundness scaffolding, the chain-aware abstract
Loop transition has a known precision limit: when a loop body
modifies a variable (e.g., `C` in merge's drain loops), the
frame eqs don't preserve that variable across the abstract
transition.  So the post-transition state is "any C satisfying
τ_inner ∧ ¬g_inner" — admitting more behaviors than the
concrete loop actually produces.

This is sound but imprecise.  The concrete cost: chain-aware
obligations whose conclusion needs relational propagation
about a modified variable across the loop become unprovable
from the chain hypotheses alone.

**Worked example.**  `merge_l2_entry_chain` (merge_two_sorted)
needs `C_s3[i+j-1] ≤ A_s3[i_s3]` at L2 entry.  When L0 exits
via `j_s2 = p_s2`, L1's loop body doesn't iterate (its guard
is false at s2), so concretely `C_s3 = C_s2`.  But the abstract
L1 transition doesn't carry "C_s3 = C_s2"; instead it asserts
τ@L1 at s3 with C_s3 free.  L1's τ doesn't include
"last ≤ A" (it dropped that atom because A is exhausted by
contract), so we can't derive the obligation about A_s3[i_s3]
at s3.

**Direction.**  Strengthen the chain-aware abstract Loop
transition with **relational propagation**: emit
`(C_out = C_in) ∨ ((∃ iterations) C_out is the result)` —
i.e., either the loop didn't iterate (vars are unchanged) OR
the loop iterated (τ_inner at s_out, vars satisfy τ_inner).
The disjunction captures the concrete loop semantics more
precisely.

**Sketch (translator change)**:
  - In `theorem_for_entry_bundle_chain` / `theorem_for_chain_bundle_chain`,
    for each Loop item in the chain, emit:
    ```
    (g_inner(in_state) = false ∧ <frame eqs for all vars>)
       ∨ (τ_inner(out_state) ∧ ¬g_inner(out_state) ∧ <frame eqs for non-modified vars>)
    ```
    Instead of the current "τ_inner ∧ ¬g_inner ∧ frame_eqs(non-modified)".

**Caveat.**  Increases the size of the chain hypotheses.  May
cause proof-engineering friction in the cite functions (which
now have a disjunction to case-split on).  Worth prototyping
on merge_l2_entry_chain first: does the relational version
let us promote that ceiling to Tier-1?

**Expected payoff.**  Would close `merge_l2_entry_chain`
without adding axioms; potentially also enables additional
chain-aware Tier-1 promotions on other future benchmarks
with similar shapes.

**Status.**  Open.  Not blocking current corpus work.

### B.4 Lean dispatch overhead — persistent process needed

**Phase X.S finding (2026-05-18).**  Each cache hit (curated
`.solved.lean` consult) invokes `lake env lean <path>` via
`synth/lean_backend/verify.py:_typecheck`.  Warm cost: 3-5s per
invocation (cold mathlib import: 10s+).  Even with pre-compiled
Basic.olean / mathlib oleans, the lake/lean startup is ~3s
fixed overhead.

For axiom-heavy benchmarks (modular_exp, kadane, majority) with
~100 PLDI'09 attribute classes:
- All-cache-hit case: 100 × 3s = 5 min of pure Lean overhead.
- Mixed (50 cache hits, 50 generic-chain timeouts at 15s):
  150s + 750s = 15 min total Lean dispatch time.
- Empirically, modular_exp wedged past 30 min even with a full
  16-companion cache; kadane wedged past 25 min with 73
  companions.  Wall-clock dominated by Lean dispatch, not Z3
  search.

**Optimization paths:**

1. **Persistent Lean process via LSP.**  Run one
   `leanmk`/`lake env` process holding mathlib + SynthLean.Basic
   loaded.  Feed obligations via stdin/LSP requests.  Each
   check becomes ~tens-of-ms (typechecking without process
   startup).  Effort: substantial — Lean Server Protocol or a
   custom REPL.  Estimated 10-100× speedup on cache hits.

2. **Whitelist-based skip.**  Maintain a `.checked` file under
   `lean/SynthLean/Y2Corpus/` containing (path, content-hash,
   toolchain-version, last-checked-timestamp) tuples.  Skip
   `lake env lean` when whitelisted.  CI's
   `tests/test_y2corpus.py` regenerates `.checked` after every
   successful run.  Effort: small — a few hundred LOC.
   Tradeoff: trust the whitelist over re-validating;
   regenerate per toolchain bump.

3. **Hash-based content-check.**  Instead of running lake,
   compute a SHA of the Lean file + axioms it imports + Lean
   toolchain version.  If the SHA matches a known-good entry,
   skip.  Same trust model as (2) but no file maintenance.

Sequencing: (2) is fastest to ship and gives most of the gain
for the curated-cache path.  (1) is the proper long-term fix
needed before Phase Y.2 (driver-LLM authoring Lean proofs on
the fly).  Track as Phase Y.1.6 candidate work.

---

## §D. Phase plan (unified roadmap, 2026-05-17)

Ring 1 + Ring 2 of the Lean backend landed, AND Phase Y.1.5
(chain-bundle translator + curated `.solved.lean` cache) closed
the remaining axiom-heavy gap.  All five axiom-heavy benchmarks
(`fib`, `factorial`, `sum_array`, `array_product`,
`count_zeros`) now synthesize under sound default.  The
lenient `potentially_unsound = True` fallback was excised; the
field remains as a dev escape hatch.  See `SOUNDNESS.md`.

The next phase is **scale**: handle HumanEval+/MBPP+-class benchmarks
end-to-end from English to (code, proof).  The plan ties together
four previously-separate threads — §A (LLM front-end), §B (Lean
backend), benchmark scaling, and proof-artifact emission — into a
sequence whose phases share work.

### D.1 Phase X: benchmark scaling + corpus building (DONE, 2026-05-18)

**50 benchmarks committed across 9 batches.**  Coverage spans
scalar arithmetic, array manipulations and reductions,
parametric searches, predicate folds, multi-output reductions,
in-place transformations (rotate/shift/reverse/swap), conditional
branching (SB(n=2), SB(n=3), SB(n=4)), nested loops, recursive
procedures (6 variants), 2D arrays, quantified atoms, and 11
axiom-heavy benchmarks via uninterpreted-function recurrences
(`factorial`, `fib`, `sum_array`, `array_product`, `count_zeros`,
`count_equal`, `dot_product`, `sum_first_k`, `array_neg_count`,
`gcd`, `power_of_two`).  See `CLAUDE.md` "Current phase" for the
batch breakdown.

**Synergy with §A.**  Each benchmark naturally yields an
(English description, `Problem` object) pair.  Combined with the
current ~30 benchmarks, we end up with an **~80-pair corpus**.
That corpus is the ICL / fine-tuning data for the driver-LLM in
Phase Y.

Concretely, we want each benchmark file to include:

- An explicit English `description` (top-of-file docstring is
  fine, but should be **the spec** as a user would phrase it, not
  the implementer's notes).
- The `Problem` object, complete with template, atoms, axioms.
- For axiom-heavy benchmarks that route through Lean fallthrough:
  `Problem.dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/<bench>"`
  so failed Lean obligations are captured for the Phase Y.2
  corpus.  Captured `.failed.lean` files pair with hand-written
  companions — `.solved.lean` (proof of the same obligation) or
  `.invalid.lean` (mechanically-verified existential
  counterexample, `∃ vars, hyps ∧ ¬ goal`).  CI runs
  `tests/test_y2corpus.py` to keep companions in sync with the
  toolchain.  See `lean/SynthLean/Y2Corpus/README.md` for the
  protocol.

Actual duration: ~2 weeks in concentrated session work (per
batch: write 5-8 benchmarks, verify each individually, defer
quick-regression for periodic runs).  Most time was actually
the Phase Y.1.5 chain-bundle Lean translator work, which
unblocked the axiom-heavy benchmarks; the benchmark authoring
itself was fast once the foundation was in place.

### D.1.5 Phase X.S: stretch corpus — confidence at the edges

**Motivation (2026-05-17).**  Phase X covered the **basics**:
50 benchmarks span scalar arithmetic, array reductions, simple
transformations, conditional branching, recursive procedures,
nested loops with quantified invariants, and a handful of
axiom-heavy UF recurrences.  What it didn't cover are problems
genuinely *hard* to verify — neither for SMT nor for a Lean
backend with the current translators.  The stretch milestone
adds 10 such benchmarks, in two clusters:

**(a) Hardest HumanEval+ / MBPP+ representatives (5).**  If we
can solve and prove these end-to-end, we have credible evidence
the synthesizer + Lean pipeline scales to **the full
HumanEval+/MBPP+ surface**, not just the 90th-percentile easy
problems.

  1. **`binary_search`** — bisection on a sorted array with the
     spec "return an index `i` such that `A[i] == x` if `x` is
     present, else return `-1`".  Hard because the post is
     existential / case-split (present vs. absent); the τ needs
     to express "search window `[lo, hi]` contains every
     occurrence of `x`, if any" plus sortedness as a UF axiom.
  2. **`merge_two_sorted`** — interleave two sorted input arrays
     into one sorted output of length `n+m`.  Three sortedness
     invariants and a counter `i + j == k`; the inductive needs
     to show the new output element is ≥ every previously
     emitted element.  Likely needs a `sorted_prefix` UF axiom
     and quantified atoms over three arrays simultaneously.
  3. **`majority_element`** — Boyer-Moore voting: single-pass
     candidate + counter.  Non-obvious invariant: "if a majority
     exists, the current candidate is it OR the counter is 0".
     This is genuinely hard — the proof of correctness requires
     a counting argument (count of occurrences of `candidate` in
     processed prefix), so we'll need a `count_eq` UF axiom and
     careful case-split on the counter being zero vs. positive.
  4. **`kadane_max_subarray`** — running maximum of contiguous
     subarray sums.  Two coupled invariants: best-so-far and
     current-ending-here.  Post is existential
     (`∃ i, j. A[i] + … + A[j] == best`); the proof needs
     `sum(A, i, j)` UF axioms and reasoning that any subarray
     ending after the current cursor is bounded by the
     current-ending-here value.
  5. **`edit_distance`** — Levenshtein DP, 2D table, classical
     `min(insert, delete, replace) + cost` recurrence.  Similar
     shape to `lcs.py` (currently a known-timeout research data
     point); we'll attempt the Lean-fallthrough path and accept
     it as **xfail with a Lean stretch goal** if Z3 still
     wedges.  The point: edit-distance is in MBPP+, and being
     able to verify it is the credible-coverage bar.

**(b) Edge-of-open-problem algorithms (5).**  If we can verify
these — even with very long Lean proofs — we have evidence that
the **template + predicate-space search** can explore algorithm
spaces where the optimal answer isn't fully known, in line with
north star (3).  We're not claiming to *discover* novel
algorithms in Phase X.S; we're showing the infrastructure can
prove correctness of representatives from regions of the
algorithm landscape where the optimization frontier is still
research-active.

  1. **`strassen_3x3_laderman`** — 23-multiplication 3×3 matrix
     multiplication template (Laderman 1976).  Naive is 27;
     Laderman's 23 is the best published.  Smirnov has 21
     bilinear approximate algorithms; whether ≤22 over ℤ is open.
     Our template should express the *space* of 3×3 mult
     algorithms with k bilinear products (analogous to the
     POPL'10 2×2 Strassen template); verifying Laderman's 23 is
     the first step.  Real discovery (k=22?) is a downstream
     goal.
  2. **`karatsuba_deg2`** — multiplying two degree-2 polynomials
     with 6 instead of 9 scalar multiplications (Toom-3).  Same
     shape as Strassen-style template search; verifies a known
     trick generalizes.
  3. **`modular_exponentiation`** — `b^e mod m` in `O(log e)`
     via repeated squaring + bit-decomposition of `e`.  UF
     axioms for `pow(b, e)` plus modular-arithmetic axioms.
     Termination via decrease on `e` halving (we currently only
     decrease by 1 — this stretches the ranking-function
     framework to handle `e → e / 2`).  Cryptographic primitive;
     log-time termination is the load-bearing feature.
  4. **`floyd_warshall`** — all-pairs shortest paths on a graph
     with `n` vertices, triple-nested DP, classical UF
     `shortest_via(k, i, j)` axioms.  Subcubic APSP is a long-
     standing open problem — verifying the classical `O(n³)`
     version is the warmup; the template space might admit
     witness-of-no-shorter-path tweaks.
  5. **`boolean_matmul_3x3`** — Boolean matrix multiplication
     for 3×3 matrices.  The optimal bilinear count for 3×3
     Boolean matmul (over GF(2) or {0,1}) is open;  Strassen-
     style results don't immediately transfer because Boolean
     min/AND lacks subtraction.  Template enumerates AND/OR
     circuits up to some depth; verification confirms the
     synthesized expression matches the naive 27-AND, 18-OR
     reference.  Like Strassen 2×2, this is a setting where
     novel-algorithm discovery is plausible — if we find a
     shorter circuit, that's a real result.

**Expected outcomes.**  Realistically, several of these will be
**xfail** at first attempt — that's the point of "stretch".
The taxonomy of failure modes itself is valuable signal:

  - **Z3 wedge but Lean closes via hand-curated `.solved.lean`**:
    confirms the infrastructure is sound, the SMT backend just
    can't handle the quantifier shape.  Adds high-value
    `.solved.lean` companions to the Y2 corpus.
  - **Z3 wedge AND Lean tactic chain fails AND we can't curate
    a `.solved.lean`**: real capability gap.  Document as a
    specific blocker in `RESEARCH.LEAN.md` (e.g., "log-time
    ranking needs `ϕ = e` with decrease `e' = e / 2`, not
    currently supported").
  - **The Problem can't even be expressed in our IR**: the
    failure mode for things like `boolean_matmul_3x3` if our IR
    doesn't surface bit-level ops natively.  Each such miss
    becomes a concrete next-phase requirement.
  - **Synthesizer produces a witness but it's the naive
    algorithm, not the published optimization**: search-space
    too narrow OR cost function rewards the wrong axis.
    Genuine north-star-(3) signal — we need a richer template
    or cost proxy.

**Tracking.**  Each stretch benchmark lives in `benchmarks/`
under a `_stretch_*.py` prefix (or a `stretch/` subdirectory)
and is excluded from the default quick / slow regression
suites.  A new `tests/regression.py --stretch` flag runs them
with extended budgets and explicit `xfail` annotations on
ones we don't yet expect to close.  Successes promote to the
regular slow suite incrementally.

### D.2 Phase Y: driver-LLM, two roles

**Phase X corpus is ready (50 benchmarks).**  The driver-LLM
training-data corpus exists.  Phase Y can begin.  We expect to
fit a small driver-LLM (8B-class — e.g., Llama 3.1 8B, Qwen 2.5
7B) that plays two roles:

#### Y.1: English → `Problem` authoring

Per §A above.  ICL on the corpus, with `problem.skill` and
`debug.skill` in system context.  Iterative loop:

1. LLM proposes a `Problem` from the English spec.
2. Synthesizer runs.  Result: SolveResult / NoSolution / Timeout.
3. On failure, LLM refines (more atoms, different template,
   relaxed Pre).
4. Convergence target: ~3 iterations average per benchmark.

If ICL underperforms, fine-tune on the corpus.  ~80 examples is
borderline; we may need to data-augment by paraphrasing the
English specs.

#### Y.2: Per-instance Lean proof sketches (refined §B)

**Key strategic choice (2026-05-16):** we do NOT invest in
per-shape auto-tactic templates for the Lean backend.  Instead,
when the synthesizer hits an obligation Lean's generic tactic
chain can't dispatch, the **same driver-LLM** constructs a
per-instance proof sketch (e.g., picks `by_cases` on a specific
variable, provides intermediate `have` lemmas, names relevant
mathlib lemmas).  The sketch is compiled into a Lean file, sent
to Lean for checking; if it fails the LLM iterates.

Two passes per obligation:

  (a) **Auto-discharge**: Z3 + Lean generic tactic chain (today's
      `_GENERIC_TACTIC`).  Closes the easy ones.
  (b) **LLM-sketch**: for each remaining UNKNOWN obligation,
      driver-LLM proposes a Lean proof sketch.  Sketch → Lean
      check → refine on failure.  TWO output modes:
        - The obligation is provable but auto-discharge was too
          weak → driver-LLM produces a `.solved.lean` proof.
        - The obligation is genuinely invalid (τ subset is
          insufficient) → driver-LLM produces an `.invalid.lean`
          existential counterexample and signals the outer loop
          to enlarge the τ predicate set.

This subsumes the "per-shape tactic templates" idea: instead of
hard-coding tactics for each obligation shape (which doesn't
scale to the long tail), the LLM handles each instance.

**Training data: the Y2 corpus.**  `lean/SynthLean/Y2Corpus/`
accumulates `(failed.lean, solved.lean | invalid.lean)`
**triples** — one per attribute-class subset Lean's generic chain
couldn't close.  The corpus protocol is:
  - Per-benchmark subdirectory.
  - `.failed.lean` is auto-dumped (verbatim record of what
    Lean tried).
  - `.solved.lean` / `.invalid.lean` is hand-curated, but both
    must type-check under `lake env lean` (enforced by
    `tests/test_y2corpus.py` in CI).

The driver-LLM's training task is then: given a `.failed.lean`,
emit either a `.solved.lean` body or an `.invalid.lean` body.
Mechanical checking guarantees the corpus can't lie — every
"this is invalid" claim is backed by a Lean-verified existential
counterexample.  See `lean/SynthLean/Y2Corpus/README.md`.

#### Why one LLM for both

Same model, same prompt-engineering effort, same fine-tuning
budget.  The skill files (`problem.skill`, `debug.skill`) become
the system prompt; the corpus becomes the example set; Lean proof
sketches become the same kind of structured output the LLM is
already producing for Problem authoring.

Expected duration: **~4 weeks for Y.1 + Y.2 prototype** once the
corpus is built.

### D.3 Phase Z: emit checked proof artifacts (deferred)

Make the "code + proof" promise real: alongside synthesized
C/Python/Rust, emit a Lean theorem file that proves the
synthesized code meets its spec.  Lean-checked at build time.
Closes the gap between **proof annotations** (what we have) and
**proof-carrying code** (what users care about).

Deferred: this is the most direct of the four directions, with no
unresolved open research questions, so it's the safest to leave
for after Phase X+Y.  Specifically: Phase Y's Lean integration
already produces proof artifacts internally; Phase Z just polishes
that into a stable user-facing format.

Expected duration: **~2 weeks** once Phase Y exposes the
artifacts.

### D.4 Sequencing notes

- **Phases X and Y.1 build in parallel.**  Every benchmark added
  is a corpus example for Y.1.  Once corpus crosses ~50 pairs,
  start Y.1 ICL experiments.
- **Phase Y.2 starts when Y.1 has a working driver-LLM.**  Same
  model, just a different prompt template.
- **Each benchmark in Phase X that wedges synthesis is a probe
  for what's missing.**  Phase X failures inform Phase Y's
  driver-LLM training (negative examples) and reveal framework
  gaps to fix in parallel.

### D.5 Open questions

- **Corpus quality vs. quantity.**  Are 80 pairs enough for ICL?
  For fine-tuning?  Need empirical signal.
- **Driver-LLM tactic granularity in Y.2.**  Sketch a whole proof
  vs. propose one tactic at a time?  The whole-sketch approach is
  faster per attempt but harder to learn; one-tactic-at-a-time is
  the LeanDojo / Lean Copilot shape.  Likely start with whole-
  sketch and fall back.
- **Skill file evolution.**  `problem.skill` was authored for
  human-readers / static-context LLMs.  As Y.1 iterates, the
  skill file should evolve to maximize LLM convergence — that's
  itself a research question.

---

## §C. Why both directions are post-foundations

These threads expand the system *outward* (LLM front-end) and
*upward* (more powerful proof backend).  Pursuing them before the
SMT path is robust would invert the dependency — a fragile core
with two unproven extensions is worse than a solid core with one
clear extension queue.

Concretely, both are blocked on:

- **Phase 5+ (source emitters) working on real-world examples.**
  The LLM front-end isn't worth building until the synthesizer
  produces deployable code on a broad benchmark class.
- **The constraint-emission centralization (Lesson #29) being
  battle-tested.**  Every emission gap surfaced now (via the
  current debug work) is a future LLM-driver-debugging session
  avoided.  The skill files need to reflect a settled API surface,
  not one mid-refactor.
- **A meaningful enough benchmark suite (~50 algorithms) to
  evaluate the LLM front-end empirically.**  Too small a suite
  and we can't tell whether the LLM-driver works in practice; too
  narrow a suite and we'll over-fit the skill files to the cases
  we have.

When these are in place, both threads become tractable.

---

## §E / §F / §G — moved (north-star expansions)

The implementer-facing expansions of the three north stars
(resource-bounded synthesis, module-level synthesis, novel
program discovery) moved to
[`PRINCIPLES.md`](./PRINCIPLES.md) under the **NS-1 / NS-2
/ NS-3** sections on 2026-06-07.

## §L — moved (governing principle)

The "framework improvements over single-case fixes"
principle moved to [`PRINCIPLES.md`](./PRINCIPLES.md) as
**P-1** on 2026-06-07.

---

## §H. The two-cost problem and the proposed combo fix

**Phase X.S finding (2026-05-18).**  The
`modular_exponentiation` and `majority_element` stretch
benchmarks both surfaced the same shape of failure:
"per-class valid but globally inconsistent" with **75-86%
cache hit rate on Lean fallthrough**.  The curated
`.solved.lean` files DO work — they close the per-class
inductive obligations — but the bundle-post obligation isn't
covered, and global SAT fails to find a τ-subset that
simultaneously satisfies all 8 constraints.

The architectural costs are TWO and they COMPOUND:

1. **PLDI'09 enumeration explosion.**  2^|τ| × |constraints|
   classes per benchmark.  modular_exp's 5-atom τ × 8
   constraints = ~256 classes.  Each class needs verification.
2. **Per-class verification cost.**  Z3 wedges on axiom-heavy
   universals → Lean fallthrough → `lake env lean` invocation
   at 3-15s/call.  Even with 86% cache hits, the remaining
   14% × N classes × 15s blows past wall budgets.

We're stuck in the worst-of-both-worlds: enumeration is slow
AND we still need extensive custom Lean code per τ-subset.
This phase's research direction is to address BOTH costs via
two coordinated changes.

### H.1 Direction (a): Tier-3 helpers + content-pattern cache

The current `.solved.lean` cache is **hash-keyed** — each τ
subset gets its own theorem (and proof) under a unique
content-addressable hash.  For bundle-post obligations where
the proof depends on the algorithm's correctness theorem (not
on the specific τ subset), this is the wrong abstraction:

- Boyer-Moore's bundle-post is the same theorem regardless of
  which τ subset includes the ∀v counting invariant — it
  always derives `count_eq(A, n, candidate) > n // 2` from
  the invariant + pre.
- modular_exp's bundle-post similarly: given the modular
  product invariant + `0 ≤ result < m`, derive
  `result = pow(b, e) % m`.

**Proposed framework change:**

Introduce a notion of "Tier-3 helpers" — Lean theorems
parameterized on the τ atoms they require, stored once per
benchmark.  Each `.solved.lean` cache hit is replaced by a
pattern-match against the available Tier-3 helpers:

  - Helper declares: "given atoms {A1, A2, …}, the obligation
    `<goal-template>` is provable."
  - When a `.failed.lean` is generated, the cache lookup checks
    if any Tier-3 helper's required atoms are a SUBSET of the
    current τ subset, AND the goal-template matches.
  - On match, the cache returns valid; otherwise fall through
    to generic chain.

This unifies the per-class curation cost.  ONE Tier-3 helper
per algorithm (or per constraint kind) replaces N hash-keyed
`.solved.lean` files.  The N files become codegen-shims
(generated by a script, each citing the helper).

**Implementation sketch:**

- Extend `synth/lean_backend/verify.py:_consult_companions` to
  match by goal-template + required-atom-set in addition to
  hash.
- Add a `.helpers.lean` file per benchmark dir that declares
  the Tier-3 theorems.
- A future commit `bm_post_from_inv.helpers.lean` for
  majority's bundle-post.  Similarly
  `pow_post_from_inv.helpers.lean` for modular_exp.

### H.1.PROTOTYPE: First Tier-3 helper landed (2026-05-18)

Working prototype for modular_exp's bundle-post:

  - `lean/SynthLean/Y2Corpus/modular_exponentiation/Helpers.lean`
    (74 lines) declares `SynthLean.ModExpHelpers.post_from_inv`
    — given the 5 required τ atoms (`exp ≥ 0`, `m ≥ 1`,
    modular product invariant, `result ≥ 0`, `result < m`) +
    the loop-exit hypothesis, derives `result = pow b e % m`.
    Hand-written, ~12 lines of actual proof body.
  - `sc7_fallthrough_SAMPLE_FULL_TAU.solved.lean` (43 lines)
    demonstrates the shim pattern: theorem statement matches a
    hypothetical sc7 dump with full τ, proof body is a 4-line
    `exact ... post_from_inv ...` citation.

To make the helper file build, `lean/SynthLean.lean` (the
library root) was updated to `import
SynthLean.Y2Corpus.modular_exponentiation.Helpers`.  The
helper compiles into `.olean` cache and is importable from any
shim under the same lake project.

**Quantitative comparison** (target: modular_exp sc7's 7
hypothetical Run-2 τ-subset variants):

| Approach   | Hand-written lines | Codegen lines | Total |
| ---        | ---:               | ---:          | ---:  |
| Tier-1 (per-subset proof) | 7 × 112 = **784**  | 0   | 784   |
| Tier-3 (helper + shims)   | **74**             | 7 × 43 = 301 | 375 |

**52% smaller, ~10x reduction in hand-written content.**

Note: the actual sc7 dumps the synth would produce are
**parameterized by which τ atoms are present**.  Subsets
missing required atoms (e.g., no `result < m`) get
`.invalid.lean` Tier-2-helper-axiom counter-example records
rather than shims.

**Next steps**:

The shim-WRITING work is left to either human curators (today)
or the driver-LLM (Phase Y.2).  A codegen script generating
shims from `.failed.lean` was REJECTED as a direction — when
Phase Y.2 lands, the driver-LLM writes the shims directly
(citing helpers), and a codegen script doesn't transfer to
that workflow.  The synthesizer's responsibility is the
**helpers** (algorithm-correctness theorems), not the
mechanical shim files around them.

  1. **majority_element Tier-3 helper landed (2026-05-18)**.
     `Helpers.lean` declares `SynthLean.MajElemHelpers.
     majority_post_from_inv` with the Boyer-Moore correctness
     statement.  Proof uses `sorry` (warning, not error) to
     EXPLICITLY document the gap: the user's invariant alone
     doesn't suffice, and we're trusting the classical
     1981 result.  A future curator can replace `sorry`
     with a structural-induction proof; the per-subset shim
     files need NO update when this happens.
  2. Tier-3 helpers for OTHER constraint kinds (sc0 entry-
     bundle, sc2 odd-branch inductive, etc.) — add as
     specific obligations need them.
  3. Optional framework change: extend
     `_consult_companions` to resolve cache hits by
     pattern-match against helper goal-templates,
     eliminating the need for per-subset shim files
     entirely.  This makes the Tier-3 layer first-class in
     the synthesizer.

### H.2 Direction (b): Unsat-core-driven subset pruning

PLDI'09's attribute-class enumeration is uniform: 2^N
subsets per constraint.  But many subsets are **strictly
weaker** than others — e.g., `{0 ≤ result}` is weaker than
`{0 ≤ result, result < m}`, so anywhere the stronger subset
fails, the weaker subset fails too; and where the weaker
subset is needed, the stronger one suffices.

**Proposed pre-filter step:**

For each constraint, before enumerating all 2^N subsets:

1. Ask Z3 to prove the constraint with the **FULL τ** as
   assumptions.
2. If valid, extract Z3's **unsat core** of τ atoms — these
   are the atoms ACTUALLY USED in the proof.
3. Mark this constraint's "required atoms" as the unsat core.
4. The constraint's candidate τ subsets are now the power set
   of `required_atoms` (or just `required_atoms` itself if we
   want one solution, not all).

For modular_exp's bundle-post: instead of 32 subsets to
enumerate, Z3 tells us "these 3 atoms are needed".  Save 29
checks.

Across the 8 constraints, the global SAT then asks: find a
single τ subset that includes `required_atoms[c]` for every
c.  This is a much smaller SAT problem (linear in N rather
than exponential).

**Why this is better than the current approach:**

- The current monotonicity-aware enumeration (Phase 3.L)
  helps single-position atoms but doesn't address
  cross-constraint sharing.
- Unsat cores give the synthesizer DIRECT INFORMATION about
  which atoms each constraint needs — instead of inferring
  via enumeration.
- The "useful subset" question is answered upfront, not
  discovered.

**Caveats:**

- Z3's unsat core is over-approximate (may include unused
  atoms).  Empirically usually tight, but could be tighter
  via min-unsat-core algorithms.
- For axiom-heavy obligations where Z3 returns UNKNOWN (not
  VALID), there's no unsat core to extract.  Fall back to
  enumeration over the remaining (Lean-decidable) atoms.

### H.3 Sequencing

Direction (b) is a synth-internal change that doesn't require
Lean infrastructure.  Implement first — measure how much it
shrinks enumeration on modular_exp / majority.

Direction (a) requires both a curation effort (write the
Tier-3 helpers per benchmark) AND a framework change (pattern-
match cache lookup).  Implement after (b) lands; the two
compose multiplicatively (b reduces classes; a reduces per-
class work).

Both unblock the "we need extensive custom Lean" cost; if (b)
alone is enough to make Z3 + minimal Lean curation tractable,
we may not need (a) at all.  This is the right experiment to
run.

### H.2.PROTOTYPE: Findings from the first attempt (2026-05-18)

Prototype implemented in `synth/solver.py` behind the flag
`Problem.use_unsat_core_fast_path` (default False; currently
hard-disabled pending a fix).  The infrastructure is in place
(BOTH-position τ identification, unsat-core extraction via
Z3 assumptions API) but the fast path is **unsound for
benchmarks with BOTH-position distractor atoms**.

**Findings:**

1. **Z3 unsat-core extraction with `solver.check(assumptions)`
   is sensitive to solver state.**  Reusing the cached
   `verifier` solver (which has axioms pre-asserted and
   accumulates push/pop state) produced spurious UNSAT
   verdicts that disagreed with substitution-based checks on
   the same body.  Using a FRESH `z3.Solver()` per check
   resolved the divergence.

2. **"Try all τ True" is UNSAFE for BOTH-position atoms with
   distractor atoms.**  intsqrt has 5 τ atoms: 3 real
   invariants + 2 distractors (`v >= x`, `i == 1`).  For the
   loop inductive, all-True τ INCLUDES the distractors in
   both pre AND post.  Z3 returns SAT (refuted) because the
   distractors don't preserve under the transition.

   The fast path then misses the valid configurations (e.g.,
   3 real invariants True, 2 distractors False).  Effectively
   the fast path can only handle benchmarks where all-True τ
   is genuinely valid — which excludes any benchmark with
   distractors.

3. **"All-False sh" combos produce vacuous validity that
   over-relaxes the SAT.**  When my fast path also recorded
   sh-all-False combos with positive-only recording, the
   cubes became universal — letting any τ work.  Filtering
   them out avoided the over-relaxation but didn't fix the
   distractor issue.

4. **Vacuous-by-guard-contradiction cases survive the
   filtered enumeration.**  E.g., for intsqrt's inductive with
   guard `v < x` + τ atom `v >= x`, the antecedent is
   self-contradictory → unsat-core empty (or trivial).  My
   fast path recorded these as valid even though the resulting
   program is unsound for general inputs.

**What the prototype DID validate:**

- The unsat-core infrastructure works at the Z3 API level.
  Fresh-solver mode produces consistent cores.
- The BOTH-position vs FREE-position τ classification is
  correctly extracted.
- The per-constraint per-sh-combo iteration is structurally
  correct (just unsound).

**Next iteration plan:**

The fundamental issue is that we can't assume τ-monotonicity
for BOTH-position atoms.  Possible refinements:

  - **Bottom-up enumeration with unsat cores**: try the
    EMPTY τ subset first (only premises).  If valid for
    sufficient sh_combos, done.  Otherwise, ADD one atom at
    a time, looking for the smallest sufficient set.
  - **Z3 native ALL-SAT mode**: ask Z3 to enumerate all
    models of a parameterized τ subset, treating each
    indicator as a free variable.  Each model = a valid τ
    subset.  Z3's all-sat extracts cubes natively.
  - **Use Z3's `param_descrs` for proof minimization**:
    `(set-option :smt.core.minimize true)` may give smaller
    cores that better identify the truly-needed atoms.
  - **Stay with current PLDI'09 enumeration; combine with
    H.1 (Tier-3 helpers + content-pattern cache)**: the
    real bottleneck is the per-class Lean cost, not the
    enumeration size.  Optimize the inner loop instead.

The prototype is preserved in `synth/solver.py` (disabled)
as the starting point for the next iteration.

### H.2.CODEGEN: Helper-citation codegen module (2026-05-19)

**Landed**: `synth/lean_backend/codegen.py` — a structural-wrapper
codegen module that replaces the generic Lean tactic chain with
a one-line `exact <helper> <args>` citation when a Tier-3 helper
matches the obligation's chosen-atom subset.

**Architecture (hybrid (iii) from the codegen vs templated-helpers
discussion)**:

  - Helpers carry the math (`Helpers.lean`, hand-proven).
  - Codegen carries the structural citation (no semantic proofs).
  - Per-call cost drops 30-60s (generic chain) → ~2-5s (cached
    `.olean` + single-term type-check).

**Boundary contract**:

  - Codegen owns: signature derivation (translator already does
    this), citation glue `:= by exact <helper> <args>`,
    subset-matching by required-atom indices.
  - Driver-LLM / curator owns: helper proof bodies, atom
    semantics, atom-index → helper-arg mapping (in `cite`
    lambdas).

This boundary preserves the earlier rejection of codegen-as-
semantic-proof-writer.  The codegen here is what the **translator
already builds** when emitting `.failed.lean` dumps — same
plumbing, different proof body.

**Per-benchmark wire-up**:

  ```python
  from synth.lean_backend.codegen import HelperRegistry, HelperEntry

  def _cite_post_from_inv(chosen, hyp_for):
      h_k_le_n = hyp_for("tau@L0", 1)
      h_outer  = hyp_for("tau@L0", 3)
      return f"exact <module>.<helper> D' D_in n k' " \
             f"{h_k_le_n} {h_outer} h_not_g"

  _REGISTRY = HelperRegistry(
      module_path="SynthLean.Y2Corpus.<bench>.Helpers",
      entries=[
          HelperEntry(
              helper_name="<helper>",
              applies_to=lambda kind, lid, br:
                          kind == "safety-bundle-post" and lid == "L0",
              required_atoms={"tau@L0": frozenset({1, 3})},
              cite=_cite_post_from_inv,
          ),
      ],
  )
  PROBLEM = Problem(..., helper_registry=_REGISTRY)
  ```

**Translation across benchmarks**: yes.  Per-benchmark cost is
(a) write helper(s) in `Helpers.lean` — math, one-time;
(b) register entries — wiring, one-time.  After that, EVERY
τ-subset that contains the required atoms hits the fast path
automatically.

**Scaling on bigger atom sets**: yes, along two axes —
  - **Speed axis**: per-class dispatch drops from 30-60s to
    ~2-5s for matching subsets.  Linearly more τ-subsets →
    proportionally more matching subsets, each still fast.
  - **Reuse axis**: ONE helper covers EVERY superset of its
    required-atom set.  Adding "extra" atoms (beyond what the
    helper minimally needs) only STRENGTHENS τ, which the
    helper's conclusion is robust to.  Helper-matching ratio
    grows with atom count, not shrinks.

**Limitations**:

  - Subsets that DON'T match any helper fall back to today's
    generic tactic chain (30-60s).  For benchmarks where most
    subsets need helper coverage, this still wedges synthesis
    if no helper applies broadly.
  - PLDI'09's 2^N enumeration itself isn't reduced — codegen
    speeds up per-class verification, not the count.  Phase
    3.L (monotonicity-aware enumeration) is the orthogonal
    lever for shrinking the enumeration.
  - Helper requires specific NAMED atoms.  The atom-index
    convention couples the registry to the order of atoms in
    `Problem.atoms[hole_id]`; renumbering atoms invalidates
    the registry.

**Instrumentation**: `Verdict.via_helper` propagates through
solver.py.  `_helper_coverage_hint_lines` emits a line like
`Helper coverage: 312/1400 dispatches via Tier-3 helper
(22.3%); 1088 fell through to generic tactic chain.` in
`SolveResult.hints` and `NoSolution.hints`.  Lets us measure
the ratio of helper-covered subsets per benchmark — the
headline metric for whether the registry is paying off.

**Status (2026-05-19)**:
  - FW canary: `floyd_warshall_post_from_inv` cited in ~4.5s,
    `via_helper=True`.  Standalone test in
    `tests/test_helper_codegen.py`.
  - Translator extension: `theorem_for_chain_bundle` now
    accepts loops with non-SB bodies (e.g., FW's L0 with Seq
    body containing nested loops).  Uses
    `_modified_vars_of_template` to compute the modified set.
  - 12/12 Lean backend regression tests pass — no regression
    on benchmarks without `helper_registry` (they fall through
    to today's generic chain path).
  - **Phase 2 (DONE 2026-05-19)**: kadane / majority /
    modular_exp helpers all ported and validated E2E.  Each
    synthesizes the canonical algorithm (extending-vs-restarting,
    Boyer-Moore, repeated squaring):

    | Bench                    | Pre-codegen     | Post-codegen | Speedup |
    | ---                      | ---             | ---          | ---     |
    | `kadane_max_subarray`    | 600s timeout    | **70s**      | 8.5×    |
    | `modular_exponentiation` | 1800s timeout   | **70s**      | 25×     |
    | `majority_element`       | UNSAT (1487s)   | **3min**     | works   |

    Commits: 974ea31, 3003e2f, bce4c75, 437f0ce, 8e97d2b,
    09d2ea7, 97b830f.

**What we learned in validation (2026-05-19)**:

  - **ranking-* must stay on Z3** (Lesson #46).  An early
    routing experiment put ranking-decrease / ranking-lb on
    the Lean dispatch path along with safety-* and coverage.
    Result: kadane_v5 and modexp_v5 each timed out at 10 min
    under sound mode — Lean process contention (each call
    spawns `lake env lean`) blew the budget on linear-arith
    obligations Z3 handles in milliseconds.  Reverted; the
    final routing allowlist is
    `_AXIOM_HEAVY_DISPATCH_KINDS = {safety, safety-bundle-entry,
    safety-bundle-post, coverage}`.  ranking-* stays on Z3.

  - **Coverage with quantified UF axioms → Z3 UNKNOWN-rejection**
    (Lesson #47).  Several benchmarks have SB(n>1) coverage
    constraints whose validity depends on universally-quantified
    UF axioms (e.g., `paths_rec` for grid_paths; case-split
    recurrences for kadane).  Z3 returns spurious UNKNOWN under
    sound mode (no Lean fallthrough for coverage before this
    push), causing the constraint to be rejected.  Added
    `theorem_for_coverage` and routed coverage through Lean
    (omega/decide on the discharged formula).

  - **Helper short-circuit: emit ONLY the full-τ cube** (Lesson
    #48).  When a Tier-3 helper validates the full-τ subset, the
    solver short-circuits per-subset enumeration and emits a
    SINGLE cube pinning every relevant indicator True.  This is
    SOUND (no over-generalization) but loses score-minimization
    — the synthesized solution carries the full τ rather than a
    minimal subset.  An earlier H.2.PROTOTYPE attempted to leave
    indicators free (emit no cube literals); that was unsound
    because nothing then constrained the chosen atoms to match
    what the helper proved.  Per-atom helpers (RESEARCH.md task
    #170) would recover score-minimization; **DEFERRED** because
    the structural plumbing is correct and the soundness
    trade-off is acceptable.

  - **`_on_z3_sat` cross-check must be selective** (Lesson #49).
    When the main SAT layer picks an assignment, the solver
    cross-checks each constraint's validity against Z3.  For
    ranking-* this catches a misrouted Lean verdict; for
    safety-* with empty-τ + UF axioms, Z3 itself returns
    spurious UNKNOWN/SAT.  Fix: `_on_z3_sat` skips kinds in
    `_AXIOM_HEAVY_DISPATCH_KINDS` (trust the Lean dispatch).

  - **Monotonicity fast-path on Lean dispatch** (extends Phase
    3.L to the Lean path).  ANT-only single-position holes
    dispatch the empty hardest case; CONS-only dispatch the
    full hardest case.  For matching subsets, dispatches 1
    Lean call instead of 2^|free-τ|.  This composes with the
    Phase H.2 helper fast path: helper covers the BOTH-position
    holes; monotonicity covers the single-position ones.

  - **Helper coverage as a headline metric** (Lesson #50).
    `SolveResult.hints` includes a "Helper coverage: N/M
    dispatches (%)" line.  Per-benchmark numbers vary widely
    (FW canary: ~22%; kadane: most safety-* hit the helper;
    modexp: similar).  The metric tells you whether the
    benchmark's helper set is paying off, separate from
    overall wall-clock.

**Open follow-ups**:

  - **Per-atom helpers (task #170) — DEFERRED, not cancelled.**
    The full-τ short-circuit forces synth to emit the full
    atom set.  Per-atom helpers (one helper per atom-minimal
    proof obligation, with a richer cite registry) would
    restore score-minimization.  Not on the critical path
    today because the corpus benchmarks accept the full-τ
    outputs.

**Open questions for phase 2 — resolved (2026-05-19)**:

  1. **Dual-mode coexistence** (Helpers.lean vs generic
     `emit_axiom_declarations`).  Validated: benchmarks with
     `helper_registry` import the Helpers module; benchmarks
     without it fall through to the generic `user_axiom_*`
     path.  Both paths exercised in the same regression run.

  2. **Primed-vs-unprimed state vars in `cite` lambdas.**  The
     cite signatures (e.g., `cite_safety_branch` taking
     `chosen`, `branch_idx`, `hyp_for`) handle the primed-state
     convention via the translator's binder generation.  Helper
     authors only need to map atom indices to argument
     positions; the translator handles the rest.

  3. **Stable atom ordering.**  Required_atoms is keyed by
     hole_id + frozenset of atom indices.  In practice, atom
     ordering was stable across kadane / majority / modexp
     ports — no rewiring needed when adding atoms (subset
     semantics handle supersets cleanly).  Documented as a
     convention in problem.skill.


### H.4 Cardinality-ordered enumeration + general helper short-circuit (2026-05-19)

**Branched on**: `experimental/cardinality-ordered-enum`,
validated on FW + insertion_sort + full quick suite (72/72).
Merged to main after validation.  Design log:
`experimental_cardinality_enum.md`.

**Motivation**.  Even after H.2.CODEGEN landed (per-class
Lean dispatch covered by helpers), Floyd-Warshall E2E
synthesis stalled on `ranking-lb` enumeration: `sc10`
(ranking-lb L1, ant τ@L1+τ@L2 = 18 atoms) has 2^18 ≈ 262k
subsets.  Per-subset Z3 checks plus per-UNKNOWN Lean
fallback drove FW past 40 minutes wall-clock with most of
the time spent in subset enumeration.

**Three layered optimizations landed together**:

1. **Cache-only Lean for ranking-*** (`solver.py`).
   `verify_class_via_lean(..., cache_only=True)` when
   `sc.kind` is a `ranking-*` kind.  Skips the
   `lake env lean` generic-tactic-chain call (5-15s each;
   tactic chain can't help anyway without τ premises), but
   still consults curated `.solved.lean` / `.invalid.lean`
   companions.  Cuts FW's per-iteration cost ~10x without
   loss of soundness (cache hits still recover what they did
   before; cache misses just defer faster).

2. **Cardinality-ordered enumeration with monotone pruning**
   (`solver.py`).  For `ranking-*` constraints with all-
   same-position free τ (ANT-only or CONS-only) and |τ| ≥ 10,
   enumerate by ascending/descending cardinality and stop at
   the first valid subset.  Emit a cube pinning the minimal
   atoms; supersets are implicitly valid by monotonicity (the
   main SAT layer is free to combine).  Collapses 2^N to
   ~C(N,1) + C(N,2) + ... up to minimal size — typically a
   few dozen checks instead of thousands.

3. **General helper short-circuit on the Z3 path** (`solver.py`).
   The §H.2.CODEGEN short-circuit was previously gated on the
   axiom-heavy Lean dispatch path.  Lifting it to the top of
   the constraint-processing block (before any enumeration)
   makes it fire for non-axiom-heavy benchmarks too —
   crucial for `insertion_sort` whose nested chain-aware
   bundle obligation generates 60+ Lean dispatches per
   subset under the previous path.

**Results**:

| Benchmark             | Pre-opt | Post-opt | Change         |
| ---                   | ---     | ---      | ---            |
| `floyd_warshall`      | 40+ min wedge | **<60s** | E2E unlocked   |
| `insertion_sort`      | 412s    | **6.5s** | with new helper|
| `merge_two_sorted`    | ~2 min  | unchanged| no path hit    |
| `sum_array`           | 107s    | 102s     | unchanged      |
| `kadane`/`majority`/`modexp` | unchanged | unchanged | no path hit |

72/72 quick regression passes; no soundness regressions.

**Soundness invariant for the cardinality path** (banked in
SOUNDNESS.md "Cardinality-ordered enumeration ..." section):

- Only fires for `ranking-*` kinds (no τ in consequent → goal
  is `ϕ ≥ 0` or `ϕ_pre > ϕ_post`).
- Only fires when all free τ holes share the SAME position
  (all ANT-only OR all CONS-only).  Mixed positions break
  joint monotonicity.
- `_classify_atoms` + `_free_tau_position` gate the check
  structurally — no soundness gradient.

**The insertion_sort helper** (this push).
`SynthLean.Y2Corpus.insertion_sort.Helpers` adds
`insertion_sort_l1_body_inductive_chain` — a Tier-2 axiom
covering the L0 inductive when nested chain-bundle
translation routes there.  The translator change in
2b164b4 enabled translation of this previously-
NotImplementedError-skipped obligation; the helper short-
circuits it back to <5s.

**Lesson banked (#51)**:

51. **Cache-only Lean for ranking is the cheap win; cardinality
    is the heavy lift; both are needed.**  Each alone is
    insufficient: cache-only eliminates noise but leaves
    enumeration cost; cardinality cuts enumeration but
    inflates per-check cost on axiom-heavy benchmarks
    (UF E-matching gets stuck on single-atom subsets).  The
    composition wins when you also gate cardinality on
    |τ| ≥ 10 so axiom-heavy benchmarks with small τ stay on
    the original path.

52. **Translator extensions can quietly regress benchmarks.**
    The nested chain-bundle support I added for FW (commit
    2b164b4) enabled `safety-bundle-post` translation on
    obligations that previously errored out fast with
    NotImplementedError.  insertion_sort's sc5 fell into this
    newly-translatable case → generic tactic chain → 60+
    UNKNOWN dispatches → 412s wall.  Diagnosis required
    bisecting against main, not just comparing experimental
    against itself.  Mitigation: a Tier-2 helper for the
    nested obligation, short-circuiting via the lifted helper
    fast path.

53. **Soft timing-drift detection in regression.**  Added
    `tests/regression_timings.json` with last-known elapsed
    baselines; regression prints `[SLOW: N.Nx baseline]` or
    `[FAST: N.Nx]` next to elapsed time when ratio exceeds
    thresholds.  Surfaces drift during the run so you don't
    have to rerun main to diagnose.  Doesn't affect pass/fail
    (CI machines vary).


## §I. Multi-template parallel exploration (Slice C of L1.6, generalized)

**Motivating context (2026-05-23):** Slice B closed the
concrete-operations multi-CANDIDATE exploration mechanism —
the framework picks among candidate body transitions at a
fixed template.  Slice C asks the natural follow-up: pick
among candidate *templates*, where each represents a
distinct algorithm shape (linear sweep / two-pointer /
inner-search / etc.).

### I.1 Two architectures and why one is wrong

**Architecture A — single SAT with TemplateUnion.**  A new
IR node `TemplateUnion(T_A, T_B, T_C)` that `expand()`
recognizes; the synthesizer builds one ConstraintSystem with
template-indicator gates, and the main SAT picks a template
plus its body atoms in one unified search.

This is the wrong call.  Four breakdowns:

1. **No cross-template information to share.**  Templates
   have different `tau@L*` / `g@L*` / `phi@L*` hole IDs
   (different loop_ids).  They share nothing beyond the
   pre/post/inputs — and those are already known at problem
   construction time.  Unified state has no compounding
   benefit.

2. **SAT solver discovers disjointness dynamically.**  The
   solver doesn't know a-priori that templates are
   independent; it has to learn that `t_B = True` makes all
   `t_A`-gated clauses vacuous.  Wasted backtracking.

3. **PLDI'09 per-class enumeration stays N×.**  Per-class
   enumeration is per-constraint; N templates contribute N
   sets of constraints.  Architecture A batches the
   enumeration into one process but doesn't shrink the work.

4. **No parallelism.**  Z3 runs single-threaded for SAT
   search.  The framework's cleanest speedup dimension —
   cross-process parallelism — is thrown away.

**Architecture B — parallel subprocess harness.**  N
template variants run as N independent `solve()` calls in
separate subprocesses; an orchestration layer aggregates
the results.  Each subprocess solves a complete `Problem`
with one template.

This is the right call.  Architecture B:
- Each SAT instance is the same size as a single-template
  problem today.
- N-way parallelism on N cores (concurrent.futures
  ProcessPoolExecutor with 'spawn' to avoid Z3 fork
  contamination — same isolation as `tests/regression.py`).
- Per-template helpers / dump dirs stay separate naturally.
- Independent per-template timeouts: a wedged template
  doesn't block the others.
- No IR changes — pure orchestration; the framework's
  soundness story carries through unchanged.
- Score comparison happens AFTER each instance returns
  (post-hoc ranking, no normalization during search).

### I.2 The harness design

```python
from synth.multi_template import multi_template_solve

result = multi_template_solve(
    variants=[
        ("count_up",   problem_a),
        ("count_down", problem_b),
        ("recursive",  problem_c),
    ],
    parallel=True,
    max_workers=None,    # defaults to min(N, cpu_count)
)

for v in result.variants:
    print(f"{v.name:20s} {v.status:10s} {v.elapsed_s:.1f}s")
print(f"Best: {result.best.name}")
```

`MultiTemplateResult` exposes:
  - `.variants` — per-variant `VariantResult(name, status, elapsed_s, result)`.
  - `.successful` — list filtered to status="success".
  - `.best` — variant with the lowest-scoring solution
    (or None if no variant succeeded).
  - `.__bool__` — True if any variant succeeded.

The orchestration layer is ~150 LOC.  Each variant is a
self-contained `Problem` object — duplicating pre/post is
the price for clean isolation.

### I.3 What the smoke benchmark validates

A 2-variant smoke (e.g., `bench_sumi_count_up` vs
`bench_sumi_count_down` — same spec, two algorithms)
exercises:
  - Variant construction + dispatch.
  - Parallel subprocess execution.
  - Per-variant timing capture.
  - Result aggregation + ranking.
  - The harness API is ergonomic (one call, structured result).

Both sumi variants should synth in ~2-5s in parallel — total
wall ≈ max(variant times), demonstrating the parallelism.

### I.4 What changes for L1.6 specifically

After the smoke validates the architecture, the L1.6 multi-
template benchmark (`bench_l16_multi_template.py`) wraps 2-3
matching algorithm templates:
  - T_A: linear sweep (B.1/B.2/B.4's template).
  - T_B: two-pointer (left = 0, right = n-1, work inward).
  - T_C: outer + inner-search (nested loops).

Each template needs its own Tier-3 helpers — the dominant
per-template cost.  But each template's authoring is
independent work that can ship incrementally.

L1.6 status check: Slice C's harness is **necessary but
not sufficient** for the sub-O(N+E) open question.  Still
need (a) augmenting-path detection, (b) graph IR richer
than `int[][]` adjacency, (c) augmenting-path-free post.
Each is multi-week.

### I.5 What we explicitly do NOT add

- **No IR changes.**  No `TemplateUnion` node, no
  template-aware `expand()` / `decode()` / emitters.
- **No score normalization.**  Each variant scores
  independently; comparison happens at result aggregation.
- **No cross-variant pruning.**  Each variant is a black-
  box SAT instance.

Aspiration creep would shift this into Architecture A
territory; the parallel harness's value is precisely in
NOT doing those things.

### I.6 Lesson banked

**#61 — Multi-template should NOT be unified-SAT.**  The
intuition "let the SAT solver search jointly over algorithm
shapes" is wrong for our IR.  Templates don't share
indicator bits; per-class enumeration is per-template;
parallelism is the dominant speedup dimension.  When
multi-shape exploration becomes desirable, the right
architecture is an orchestration layer that runs N
independent `solve()` calls in parallel — never a single
SAT covering the union.  The unified-SAT approach
duplicates work and serializes search; the orchestration
approach amortizes the per-variant constraint generation
across cores without compounding solver overhead.


## §J. C1 — beyond the chain/clique graph class toward L1.6's open question

**Motivating context (2026-05-23):** Slice B's concrete-ops
benchmarks (B.1, B.2, B.4) and Slice C's multi-template
benchmark all share two restrictions:
  - **Graph class**: chain (`G[k][k+1] >= 1` for all k) or
    clique (`G[p][q] >= 1` for all `p ≠ q`).
  - **Spec strength**: count-bounded post (`c >= n - 1`),
    which any matching meeting this count satisfies — does NOT
    require maximum.

L1.6's open question is sub-O(N+E) on **arbitrary bipartite
graphs** with a **maximum-matching** post.  Three load-bearing
generalizations are missing.

### J.1 The three generalizations

  **(c) Sparse graph IR.**  `int[][]` adjacency is O(N²)
  storage and forces benchmarks to assume dense graphs.  Real
  matching algorithms iterate edges; sparse representations
  (edge list, adjacency list, CSR) are the natural fit.

  **(b) AP-free / maximum-matching post.**  Berge's theorem:
  M is a maximum matching iff there is no augmenting path
  (alternating between non-M and M edges, starting and ending
  at unmatched vertices).  The post `∄ AP in M` is the
  textbook maximum-matching certification.

  **(a) Augmenting-path search template.**  BFS or DFS over
  alternating edges, with path-storage and flip primitives.
  The template shape is multi-loop with auxiliary state
  (visited set, parent pointers, path buffer).

(c) is foundation; (b) defines the goal; (a) implements the
algorithm.

### J.2 Sequencing — smaller deliverable first

The full (a)+(b)+(c) is multi-week.  But there's a tractable
intermediate:

  **Maximal matching** (not maximum) on sparse graphs.  M is
  maximal iff no edge can be added without breaking the
  matching invariant.  Greedy iteration over edges achieves
  maximal: `for each (u, v) in edges: if M[u]=-1 ∧ M[v]=-1:
  pair them`.

This needs only (c) + a maximal-matching-post version of (b).
NO AP machinery, NO multi-week template changes.  Maximal is
weaker than maximum but a real step UP from count-bounded
(which doesn't even require validity beyond MI for matched
pairs).

Plan:
  - **C1.A — sparse graph IR** (edge list).  `int[]` of
    length 2m where edge i has endpoints edges[2i], edges[2i+1].
    Plus `m: int` edge count.  No framework changes — just a
    new pre/post shape that uses int[] subscripting.
  - **C1.B — maximal-matching post**.  Post shape:
    `matching-invariant ∧ ∀i ∈ [0, m). ¬(M[edges[2i]] == -1 ∧
    M[edges[2i+1]] == -1)`.
  - **C1.C — greedy matching benchmark**.  Template
    `SB() >> Loop(SB(n=2))`; body checks `M[u] == -1 ∧ M[v] ==
    -1` and pairs if so.  Concrete ops only, no UFs.
  - **C1.D — AP search + maximum-matching post** (multi-week,
    deferred).  Blocked on C1.A/B/C landing.

### J.3 What C1.A-C makes possible

A concrete `bench_greedy_match_general.py` that synthesizes
greedy matching on arbitrary bipartite graphs (no chain/clique
assumption) with a meaningful spec (maximal matching, not just
count).  Demonstrates:
  - The framework handles sparse graph specs.
  - Maximal-matching obligations close (likely needing 1-2
    Tier-3 helpers for the inductive `for-each-edge`).
  - Generalizes beyond the B.1-Slice-C benchmarks' graph
    restrictions.

### J.4 What C1.A-C does NOT do

  - **Does NOT achieve maximum matching.**  Greedy can produce
    a maximal matching that's not maximum (classical example:
    pair (0,1) on a path 0-1-2-3, missing the maximum (0,1)+(2,3)
    wait actually that's maximum; the classical example is 1-2
    in a 1-2 + 0-1 + 2-3 graph: greedy pairs 1-2 first, then
    can't pair 0 or 3, count = 2 vs maximum 2 anyway — pick
    a better example).

  Greedy on edge order CAN be suboptimal: 4 vertices, edges
  (0,1), (0,2), (1,3), (2,3).  Maximum matching: (0,2) + (1,3)
  = 2 pairs.  Greedy iterating in order: takes (0,1) first → 2
  is unmatched, 3 is unmatched but (1,3) blocked since 1
  matched; ends with M = {0→1}, 1 pair.  Maximal but not
  maximum.

  So C1.A-C produces a real algorithm with a real spec, but
  NOT a sub-O(N+E) maximum algorithm.  That stays C1.D.

  - **Does NOT close L1.6's open question.**  Maximum matching
    classical algorithms are O(E · √V) (Hopcroft-Karp) or
    O(V · E) (Edmonds).  Sub-O(N+E) on restricted classes is
    the open frontier.  C1 builds the substrate (graph IR + AP
    machinery); the open question is whether a new algorithm
    on that substrate can hit the lower bound.

### J.5 Risk

The maximal-matching INDUCTIVE on a `for-each-edge` template
may require a new Tier-3 helper shape we haven't authored
before.  The MI conjunct preservation is the same case-split
+ omega pattern from Slice B/C, BUT the new conjunct
"no-unmatched-edge-pair" is quantified over the EDGE LIST,
which is different from the per-vertex MI quantifier.  Could
need:
  - Symbolic indexing into the edge list inside the helper.
  - Case-split on whether the current edge i was the one just
    processed.

If the helper authoring takes >1 day per attempt, that's a
signal to revisit the spec or add a tactic-library entry
(per C1's expected pattern repetition).


## §K. C1.D — augmenting-path search + maximum matching

**Motivating context (2026-05-24):** C1.A-C closed greedy
maximal matching on sparse graphs.  C1.D is the remaining
piece for L1.6's open question — maximum matching via
augmenting-path detection.

### K.1 Augmenting paths — the math

In a bipartite graph G = (L ∪ R, E) with current matching M:
  - An **augmenting path** P wrt M is a simple path in G such
    that:
      - Endpoints are unmatched in M.
      - Edges alternate between G \\ M and M.
  - **Berge's theorem**: M is a *maximum* matching iff no
    augmenting path exists in G wrt M.

To improve M when an AP exists, **flip** the path: each
G\\M-edge becomes an M-edge, and each M-edge becomes a
G\\M-edge.  This increases |M| by 1 (one extra unmatched
vertex becomes matched on each side).

Length analysis (odd, since alternating, in bipartite):
  - Length 1: single edge (u, v), both endpoints unmatched.
    Flipping = pairing them.  Greedy already handles this.
  - Length 3: u → v → z → w where u, w unmatched and
    (v, z) ∈ M.  Flipping: M becomes (M \\ {(v,z)}) ∪ {(u,v), (z,w)}.
  - Length 2k+1: 2k+1 edges, k of them in M, k+1 outside.

Hopcroft-Karp finds all length-1 APs in one BFS phase, then
length-3, etc., for O(E√V) total.  Edmonds's O(VE) algorithm
finds APs one at a time via DFS with alternation.

### K.2 What C1.D requires

Three independently load-bearing pieces:

  **(a) AP-free post (Berge's theorem in IR-land).**
  Express "no augmenting path exists" as a Lean predicate +
  axiom, or as a quantified atom over potential paths.

  **(b) AP search template.**  An IR construct that searches
  for an AP given (G, M) — BFS or DFS with alternation.
  Sub-pieces:
    - Path representation: bounded-length int[] (path =
      sequence of vertex indices), with a length counter.
    - Visited / parent arrays for BFS.
    - Alternation state machine: track whether the next
      edge to explore should be in M or in G\\M.

  **(c) Flip primitive.**  Given a path, update M to flip
  the alternation.  Concrete operations on int[].

### K.3 Tractability and sequencing

The full O(E√V) Hopcroft-Karp is multi-week.  A reasonable
sequence:

  **K.3.0 — Berge axiomatically.**  Define
  `no_aug_path(G, M, n) : bool` as a Lean axiom + the Berge
  axiom `no_aug_path → is_max_matching`.  Replace the maximal
  post in `bench_greedy_match_general` with the maximum post
  via the Berge axiom.  Demonstrates the framework can EXPRESS
  the goal, even before implementing AP search.

  **K.3.1 — Length-1 AP audit.**  A benchmark that starts with
  M (some matching, maybe greedy's output) and verifies it has
  no length-1 AP.  Trivial in the maximal-greedy case (greedy
  produces this) but exercises the AP encoding.

  **K.3.2 — Length-3 AP detection + flip.**  The first
  non-trivial AP step.  Template: outer loop over unmatched u;
  inner loop over neighbors v of u; lookup z = M[v]; inner
  loop over neighbors w of z; if w unmatched, flip the path
  u-v-z-w.  Three nested loops with bounded-degree
  assumptions on G.

  **K.3.3 — General-length AP via BFS/DFS.**  Path-storage
  primitive needed.  Multi-week template engineering.

  **K.3.4 — Hopcroft-Karp's layered BFS.**  Multi-week
  research-engineering.

### K.4 Why length-3 first (K.3.2)

Length-1 (K.3.1) is too weak — greedy already saturates it.
Length-3 is the smallest case that produces a STRICTLY
LARGER matching than greedy on some graphs.  Classical
example: edges (0,2), (0,3), (1,2).  Greedy in this order:
pairs (0,2) first → 1 pair; (0,3) blocked (0 matched);
(1,2) blocked (2 matched).  Maximum: (0,3) + (1,2) = 2 pairs.
Length-3 AP from u=1: 1-2-0-3.  Flip → maximum.

Implementing length-3 is THE step where the framework
demonstrates it can go beyond greedy.  Once length-3 is
implemented, the question "what's the smallest natural
graph class where K.3.2 saturates to maximum?" becomes a
concrete research question.

### K.5 What sub-O(N+E) requires

(beyond C1.D)

The open question wants an algorithm with worst-case time
sub-(N + E) on a graph class where the bound is meaningful.
Possible angles:
  - **Restricted graph classes** with structural properties
    (e.g., interval graphs, planar graphs, bounded-treewidth
    graphs).
  - **Approximation algorithms** that produce a matching
    within a factor of maximum, in sub-linear time.
  - **Randomized algorithms** with sub-linear expected time.

Even with K.3.0-4 implemented, hitting sub-(N + E) is a
research result, not an engineering project.  The framework
+ Lean would let us VERIFY a candidate algorithm; the
algorithm itself needs to exist first.

### K.6 What this push aims for in the current session

Tractable in one focused multi-hour session:
  - K.3.0 (Berge axiomatic) — author the Lean axiomatic
    encoding of "no AP" + Berge.  Benchmark that uses it.
  - K.3.1 (length-1 audit) — a benchmark that verifies
    length-1 absence post-greedy.  Mostly mechanical.

Stretch (probably needs follow-up sessions):
  - K.3.2 (length-3 detection) — design + initial template.
    Tier-3 helpers will be substantial.

If this push delivers K.3.0 + K.3.1, it's a real milestone —
first L1.6 benchmark with a maximum-matching post (even if
the algorithm is just greedy + audit).  K.3.2 onward is
multi-week regardless.


## §K.A. Framework limit surfaced by C1.D — lambda-bound UF args

**Discovered 2026-05-24** while attempting K.3.1.5
(`bench_aug3_flip_concrete.py` — concrete length-3 AP flip
with UF-detected indices).

### K.A.1 The bug

`synth/expr.py:_translate_call` translates
`ForAll(lambda G_, n_, M_: body)` by typing each lambda-bound
variable as `z3.Int`.  This works when every UF in `body`
takes only Int args, but fails sort-check when a UF expects
`int[]` or `int[][]` and we pass a lambda-bound name:

```python
("ForAll(lambda G_, n_, M_: Implies("
 "is_matching(G_, n_, M_) == 1, ...))")
```

Here `M_` is bound as `z3.Int`, but `is_matching` declared
in `Problem.uninterpreted` as taking `(int[][], int, int[])`
expects M_ to be of `ArraySort(Int, Int)`.  Z3 raises
`Z3Exception: Sort mismatch`.

### K.A.2 Why it matters for C1.D

The K.3.2+ path wants:
  - `M : int[]` (concrete array, indexable via `M[k]`).
  - UFs over `M` for AP detection / matching properties
    (`is_matching(G, n, M)`, `matching_size(G, n, M)`,
    `find_aug3_*(G, n, M)`).
  - Axioms quantifying universally over G, n, M and applying
    those UFs.

The lambda-Int typing means axioms can't quantify over the
typed M.  Workarounds:
  - Make M an opaque `int` identifier (K.3.0's approach).
    Loses concrete indexing.
  - Use a side-channel UF `m_at(M_id, idx)` (functional array
    hacky encoding).  Loses the convenience of `Update`.
  - Restate axioms with M as a free var (not quantified).
    Loses generality — each axiom would assert only about the
    specific M in scope.

None of these are clean.

### K.A.3 The fix

`synth/expr.py:_translate_call`, around line 186-188:

```python
# Current:
for arg in lam.args.args:
    bv = z3.Int(arg.arg)
    ...
```

Change to allow a type annotation in the lambda's argument:
```python
ForAll(lambda M_: 'int[]', body)
```
or use a sentinel naming convention (e.g., `M_arr_` → int[],
`G_mat_` → int[][]).

The TYPE-ANNOTATION approach matches Python's syntax (`def
f(x: int[]) -> ...`) but Python's ast doesn't carry the
annotations through lambdas natively — would need a parser
extension.

The CONVENTION approach is simpler: parse the variable name
suffix.  `_arr` → ArraySort(Int, Int); `_mat` → ArraySort(Int,
ArraySort(Int, Int)).  Backwards-compatible (existing
benchmarks use names like `k`, `j`, `p`, `q` — all Int).

This is a framework extension (~20 LOC change in expr.py +
docs).  Banked as future work; not in this session's scope.

### K.A.4 Impact on C1.D's plan

K.3.0 still works (M is opaque int).  K.3.1.5+ benchmarks
that mix concrete matching state with UF axiomatization need
this framework extension first.  Recorded as the gating issue
for genuine K.3.2 (concrete length-3 AP detection with
UF-axiomatized "AP exists" predicate).

### K.A.5 Lesson banked

**#64**: **Lambda-bound variables in axioms are always
z3.Int**.  When designing UF-axiomatic specs that mix
concrete (`int[]`) and abstract (UF) state, every UF must
take only Int args.  Concrete arrays can be PASSED at
specific call sites (not quantified over).  If a benchmark
needs to universally quantify over a matching/array state,
the framework needs the K.A.3 extension first.


## §K.B / §K.B-REVIEW / §K.D — moved

**Moved to [`RESEARCH.COMPLETED.md`](./RESEARCH.COMPLETED.md)
(2026-06-07).**  Break-primitive design pass, design review,
and chain-aware-break design pass are all SHIPPED and live
in the completed-research archive.

---

## §M. Synthesis performance — distributed Lean dispatch (deferred)

> **Phase: deferred** — log of the right architectural direction.
> Not for now (single-machine runs); revisit when correctness
> coverage on the rest of the framework is in place.

### M.1 The cost model

K.3.2 timing curve, single-machine 8-worker parallel Lean
dispatch (2026-05-25):

| Benchmark                                  | Wall   | Lean calls |
| ---                                        | ---    | ---        |
| `bench_aug3_inner_search.py` (1-loop)      | 403s   | —          |
| `bench_aug3_two_loops.py` (2-loop)         | 578s   | 468        |
| `bench_aug3_three_loops.py` (3-loop)       | 1466s  | 1239       |
| `bench_aug3_three_loops_flip.py` (3+flip)  | 2851s  | ~1500+     |

Pattern: each added loop ~2.5× the dispatches (τ atoms cascade
linearly with depth, exponentially with subsets on BOTH-position
constraints); adding M-modification ~2× the time (axiom-heavy
case-split on store-chains).

Linear extrapolation: a 4-loop benchmark would be 5000-8000s
(~1.5-2 hours).  Untractable for interactive use.

### M.2 Where the time goes

Profile: ~99% of Lean dispatches close via the generic tactic
chain in ~4-5s each.  Of that 4-5s:

  - ~2-3s: `lake env lean <tmpfile>` startup + mathlib olean
    preload.
  - ~1-2s: tactic execution.
  - <0.1s: actual proof complexity.

In other words: **per-dispatch latency is dominated by Lean's
mathlib preload**, not by the proof.  Parallelism (8 workers)
helps but is bounded by cpu_count.

### M.3 The right architecture: distributed Lean resolver cluster

The synthesizing node should not run Lean at all.  Instead:

  - A **dedicated cluster of Lean-resolver nodes** keeps long-
    lived Lean processes with mathlib pre-loaded.  Each node
    accepts theorem-text + import-list over an RPC interface,
    type-checks, returns verdict.  Amortizes the ~2-3s mathlib
    overhead across all dispatches the node handles.
  - The synth node offloads every Lean call to the cluster.
    A load-balancer routes to the least-loaded resolver.  Per-
    dispatch wire latency is ~1ms (LAN) or ~10ms (WAN);
    completely dominated by actual proof work.
  - Cluster scales horizontally.  An N-node cluster gives ~N×
    the throughput of single-machine 8-worker parallelism, with
    no shared-machine contention (no Lean cache races, no CPU
    saturation from mathlib load × workers).

**Expected gains.**  Single-machine, single-worker steady-state:
~10× per-dispatch (eliminating the mathlib preload).  With
cluster parallelism (say 32 nodes), an additional ~4× over the
existing 8-worker parallel.  Combined: roughly **30-40× wall
on K.3.2-class benchmarks**.  The 47-min 3-nested-flip becomes
~1-1.5 min.

### M.4 Where this sits in the roadmap

This is the right move long-term but NOT the right move now:

  - Correctness coverage on the rest of the framework (Phase
    Y driver-LLM, multi-procedure synthesis §F, resource-bound
    invariants §E, NL front-end §A) is the priority.
  - Single-machine performance is good enough for benchmark
    authoring + framework validation.
  - Distributed infrastructure is a substantial engineering lift
    (RPC protocol, resolver-node container, deployment automation,
    monitoring) that should land after the rest of the framework
    is correctness-stable.

**Trigger to revisit.** When (a) a benchmark of genuine scientific
interest needs synthesis times > ~30 min on single-machine, AND
(b) the rest of the framework is correctness-stable enough that
performance is the load-bearing bottleneck, this becomes the
next push.

### M.5 Bridging optimizations (in-scope now)

Until the cluster architecture lands, the lighter-touch
optimizations are:

#### M.5.A Trivial-helper auto-generation (DONE 2026-05-25)

Branch `perf/trivial-helpers`.  Two pieces:

  1. **`SynthLean.Core` split.**  Extracted `store` /
     `store2d` defs from `SynthLean.Basic` into a Core
     module that imports nothing heavy.  `Basic` continues
     to re-export them (existing helpers unaffected).
     Measured `lake env lean` startup:
       - Core-only import:    ~1.4s per call
       - `Basic` (mathlib):    ~4.5s per call
     The ~3s diff is the mathlib olean preload.

  2. **Auto-template (`synth/lean_backend/auto_helpers.py`).**
     Conservative templater: for known auto-handleable
     constraint SHAPES (coverage / safety-bundle-entry /
     safety-bundle-post / safety), emit a Core-only proof
     body of `subst_eqs + obtain ⟨_, ..._⟩ := h_pre + first |
     omega | assumption | (refine ⟨...⟩; all_goals ...)`.
     Bails out if any binder mentions `store` / `store2d`
     (those need mathlib's simp + split_ifs).  On Lean
     failure, transparently retries with the generic-chain
     path (Basic + mathlib).

     The auto-proof is always type-checked by Lean — same
     soundness guarantee as any Lean dispatch.  False
     negatives (the templater fires but Lean rejects)
     waste ~1.4s per dispatch; the conservative shape +
     binder-store check minimizes them.

**Measured gains on the K.3.2 family** (single 8-worker
machine):

| Benchmark                  | Baseline | With auto | Speedup |
| ---                        | ---      | ---       | ---     |
| `bench_aug3_inner_search`  | 403s     | 346s      | 1.16×   |
| `bench_aug3_two_loops`     | 578s     | 325s      | 1.78×   |
| `bench_aug3_three_loops`   | 1466s    | 554s      | **2.65×** |

The gain scales WITH benchmark depth: 3-loop sees the
biggest speedup because its Lean dispatch count grows fastest.

#### M.5.B Expanded Z3 trust list (REJECTED 2026-05-25)

Considered: route more constraint kinds (`safety-bundle-entry`,
`safety`) to Z3 when their bodies are pure-LIA.  Soundness
review surfaced two failure modes:

  1. **Missed quantifier instantiation** — Z3's E-matching
     can miss instances under user-supplied axioms; spurious
     UNSAT becomes spurious VALID; main SAT picks an unsound
     cube.  This is what `_axiom_heavy_lean_path` was
     introduced to avoid.

  2. **Quantified-array reasoning (lesson #65)** — even
     WITHOUT user-supplied axioms, Z3 mishandles
     `ForAll(lambda k: ... M[k] ...)` shapes when `M` is
     written via `Update`.  This is the load-bearing reason
     K.3.2 family benchmarks use the `["0 == 0"]` dummy-axiom
     trip-wire to force Lean routing.

A safe expansion would need a per-OBLIGATION shape check
(no quantified atoms in body).  But K.3.2-family τ atoms
ARE quantified (the MI atom), so most K.3.2 obligations
would still route to Lean — the expansion buys little on
the benchmarks we care about most.

**Decision: skip the Z3 trust list expansion.**  The
soundness risk is real, the gain on K.3.2 family is small,
and the auto-helper path already covers the high-ROI shapes.

Both `M.5.A` (landed) and the deferred cluster architecture
(`M.3`) compose orthogonally: auto-helpers reduce the
DISPATCH count when shapes match; the cluster reduces the
per-dispatch latency.  Stacked gain on K.3.2-family:
~2.5× (auto-helpers) × ~30× (cluster) = ~75× wall — the
47-min 3-nested-flip becomes ~30-40s.

### §M.PARKED Narrower Z3-suspect filter (moved from plan §11.3)

Today's axiom-heavy bypass (Phase Y.1.5) routes ALL classes of
soundness-critical constraints through Lean when the problem has
UFs/axioms.  This wastes Z3 fast paths on classes Z3 could
correctly accept — Z3 UNSAT verdicts are sound everywhere
(axioms only restrict the model space; UNSAT-under-axioms ⇒
UNSAT-anywhere).

**Refinement (parked for speed work):**

Instead of `_is_axiom_heavy = (UFs or axioms)`, use
`_z3_potentially_unsound_verdict = (any quantifier in body OR
axioms in scope) AND vr in {SAT}` — only Z3's SAT verdict is
suspect.  UNSAT stays trusted (always sound); UNKNOWN dispatches
to Lean (existing path).  This narrows the slow-Lean path to
actually-suspect verdicts and should cut axiom-heavy synthesis
time substantially.

Implementation:
  1. Detect quantifiers in `sc.body` (walk for `z3.Quantifier`
     nodes).
  2. Run Z3 first.  If UNSAT → accept.  If UNKNOWN → existing
     Lean fallthrough.  If SAT on axiom-heavy + quantified →
     route to Lean (full dispatch, not just cache lookup).
  3. Keep cache fast-path on top.

Defer until after the `.solved.lean` curation push lands and we
have measurements of the slowdown the current "skip Z3 entirely"
imposes.  Could also drop the bypass entirely if the cache
covers enough valid-class signatures.

---

## §N. HumanEval+ coverage — triage shipped, expansion TODO

**Status (2026-05-28)**: triage of all 164 HumanEval+ problems
landed at top-level [`HUMANEVAL.STATUS.md`](./HUMANEVAL.STATUS.md)
(commit `312b202` on main).  Per-problem 5-level rubric
(GREEN / YELLOW / ORANGE / RED / BLACK) with cited blocker
for each non-GREEN rating.

### Headline distribution

  - **GREEN  47 (28.7%)** — drop-in ready today.
  - **YELLOW 19 (11.6%)** — Tier-1 helpers needed; cost is
    Slice-2.C / GS-class proof engineering.
  - **ORANGE 32 (19.5%)** — minor framework extension
    (string-as-`int[]`, fixed-point Real, digit-arithmetic
    axioms, variable-length output).
  - **RED    10 ( 6.1%)** — major framework work (set/dict,
    ragged 2D, graph IR).
  - **BLACK  56 (34.1%)** — out of scope under current
    direction (genuine string semantics, file IO, hashlib,
    `eval`, randomness, dynamic typing).

### What this opens up

  - **40% reachable today** (GREEN + YELLOW = 66 problems)
    with existing framework + per-benchmark proof
    engineering.
  - **~60% reachable** (~98 problems) with three framework
    sessions:
      1. **String-as-`int[]`** (~15 unblocks): palindrome,
         bracket balance, digit counting, char filtering,
         length predicates.
      2. **Fixed-point Real** (~10 unblocks): float-
         arithmetic problems.
      3. **Variable-length output array** (~8 unblocks):
         problems where output length depends on input.
    Each is a ~1-2 session framework push followed by
    benchmark authoring; together they would deliver a
    ~58-problem expansion.

### Future direction (deferred)

This is a research-direction signpost, not a current phase.
Three natural follow-up pushes once L1.6 / matching work
stabilizes:

  1. **Validate the GREEN rating** by authoring 5-10
     high-confidence GREEN problems end-to-end (HE/3, HE/13,
     HE/49, HE/60, HE/97, HE/121, HE/150 are the suggested
     candidates).  Cost: ~1-2 sessions.  Goal: confirm the
     triage matches reality.
  2. **String-as-`int[]` framework extension**: highest
     coverage-per-session.  Includes an ASCII axiom library
     for `length`, indexing, slicing windows, `ord` /
     `chr` identity, and per-character class predicates.
     Cost: ~1 framework session + per-benchmark authoring.
  3. **Fixed-point Real** extension: covers the float
     subset.  Encode as `(num: int, denom: int)` or
     `int * 10^k` fixed-point.  Cost: ~1-2 framework
     sessions.

The methodology was triage-only — no synthesis attempts.
The blocker citations in the per-problem section identify
what's needed to flip each YELLOW / ORANGE / RED to GREEN,
so the doc serves as a roadmap rather than a static
classification.

### Caveats

The triage is based on canonical solution shape, not on the
underlying mathematical content.  Some YELLOW ratings could
turn out to be RED if the required spec atoms aren't
tractable; GREEN does NOT mean "easy" — it means "no
framework blockers."  The 34% BLACK is the realistic ceiling
under the current direction unless we commit to a string
theory (a multi-month framework push out of scope for any
near-term phase).

---

## §O. Claude Suggested Directions (merged from research.claude.md, 2026-06-07)

Unprompted research ideas surfaced during implementation
work, written by Claude (the LLM, not the project owner).
Originally lived in `research.claude.md`; merged in 2026-06-07
to consolidate the research surface.

Each entry has:

  - **Idea** — one sentence.
  - **Why it's interesting** — what gap it would close /
    what new affordance it would unlock.
  - **What suggested it** — concrete moment in the
    implementation work that crystallized the idea.
  - **Effort sketch** — rough order of magnitude.
  - **Status** — `draft` / `endorsed` / `dropped` /
    `promoted to RESEARCH.md`.

Mature proposals get promoted to a top-level § in this file
(see the "Promotion process" subsection below).


## P1 — Solution-count regression as a soundness oracle (formalized)

**Idea.** Bake the "if a benchmark suddenly returns more solutions,
something dropped a constraint" signal directly into the regression
suite as an explicit per-benchmark expected solution count.  Today
it's an *implicit* sanity check (the maintainer notices the
number); make it explicit and let CI enforce it.

**Why it's interesting.** Lessons #30, #31 in CLAUDE.md describe
how `rec_zero_array` going 1 → 3 solutions after the Phase 5.B++
centralization caught a generator-exhaustion bug that no other
test would have noticed.  This is a free soundness oracle, but
right now it requires the maintainer's eye to notice.  Per-bench
expected-count assertions would catch the same class of bug
automatically.

**What suggested it.** Lesson #31 itself.  And the realization
that the cover_*_branched_recur benchmarks are doing exactly this
manually (assert `args[n] == "n - 1"` after solve), but only for
one specific obligation.  A `max_solutions=N` + `expected_count=N`
contract per benchmark would generalize.

**Effort sketch.** Half a day.  Add `expected_solutions: int` to
`Problem` (or to the regression suite's benchmark registry); have
`tests/regression.py` fail on mismatch instead of just print.
Pick conservative bounds — e.g., `expected_solutions=1` for
benchmarks with strong specs, looser for the underspecified ones.

**Status.** Promoted (implemented `2026-05-15`).  Lives as
`Problem.expected_solutions: int | None`; regression suite fails
on mismatch with a `SOLUTION-COUNT MISMATCH` message.  All 28
benchmarks annotated with current counts.  CLAUDE.md Lesson #38.

---

## P2 — UNKNOWN-conservative-as-REJECT for soundness-critical kinds

**Idea.** Treat Z3 `UNKNOWN` on safety / coverage / ranking
validity checks as conservative-REJECT instead of conservative-
ACCEPT.  Two-level fallback to avoid breaking axiom-heavy
benchmarks: (a) per-constraint, promote deferred UNKNOWNs if the
strict pass leaves zero confirmed-valid classes; (b) globally,
retry with all deferred classes promoted if the strict-pass main
SAT returns UNSAT.

**Why it's interesting.** This was a real, currently-active
soundness gap.  The Python emitter's runtime check (Phase 5.C)
caught it on `max_array`: when phi=`i` was picked under Z3
nondeterminism, `proof_decrease(i_out, i_in)` fired immediately.
The first pass at a fix (narrow REJECT to ranking only) wasn't
enough — max_array also had a UNKNOWN-conservative-ACCEPT gap on
the invariant `m == A[0]`.  Extending REJECT to safety + coverage
fixed max_array but UNSAT'd fib (axiom-heavy; every safety check
on quantified `fib(k)` atoms returns UNKNOWN).  The two-level
fallback is what lets both ride the same policy.

**What suggested it.** `max_array` flaking the Python emitter
tests with `decrease: L0 ranking decrease (prev=1, curr=2)`.  The
synthesizer claimed phi=`i` was a valid ranking; the emitted code
proved it wasn't.

**Effort sketch.** Small — landed in this push.

**Status.** Promoted (implemented `2026-05-14`).  Implementation
in `synth/solver.py:_REJECT_UNKNOWN_KINDS` + the per-constraint
and global two-pass fallback in the enumeration loop.  All 27
benchmarks (including fib) still pass; `test_max_array_runtime_check`
is back online as a soundness regression guard.  CLAUDE.md
Lesson #33.

---

## P3 — Self-instrumenting synthesized binaries with constraint telemetry

**Idea.** The Python emitter's `runtime_check=True` mode currently
emits assertions.  Extend it (or add a third mode) to emit
*telemetry* — log which atom was needed when an obligation
fired, count invocation paths, dump a profile of which τ atoms
were load-bearing at runtime.  The LLM driver (`RESEARCH.md` §A)
can use this telemetry to adaptively prune the predicate space:
atoms that never participate in any runtime check probably
aren't needed in the next iteration.

**Why it's interesting.** Today the LLM driver's signal for
"this atom mattered" is purely synthesis-side: did Z3 select it?
But Z3-selection is heuristic and may favor atoms that "happen to
work" without being load-bearing.  Runtime-side telemetry shows
which atoms are *actually* exercised — a different and possibly
stronger signal.  Could shorten the LLM-driver convergence loop.

**What suggested it.** Writing `synth/proof_runtime.py` and
noticing that the `ProofViolation` exception carries structured
`(kind, message, details)` fields ready for telemetry.  Trivial
extension: log on success too, not just failure.

**Effort sketch.** Medium.  A few days for the instrumentation
mode in the emitter, plus a sketch of how the LLM driver consumes
the telemetry.  Most of the work is in the *consumer* design, not
the instrumentation itself.

**Status.** Draft.  Compelling enough that I'd start it after P1
and P2.  Dovetails with `RESEARCH.md` §A.

---

## P4 — Hybrid SMT-Lean dispatch on goal shape

**Idea.** Rather than picking SMT or Lean for the whole problem
(`RESEARCH.md` §B currently frames them as alternatives), route
individual proof obligations to whichever backend fits best.
Quantifier-free arithmetic → SMT (fast, complete-ish).  Structural-
induction or dependently-typed-spec obligations → Lean.  The
synthesizer's `SafetyConstraint.kind` already distinguishes
constraint shapes; extend the dispatch.

**Why it's interesting.** `RESEARCH.md` §B currently sets up
SMT-vs-Lean as a fork ("we might pursue Lean rather than PINS").
But a real synthesis problem mixes constraint kinds — the
inductive constraint on a quantified loop invariant might want
Lean, while the LB on `n - i` definitely wants SMT (Z3's
`omega` arithmetic is plenty).  Per-constraint dispatch lets
each backend do what it's good at.

**What suggested it.** The constraint-kind taxonomy we already
have (`safety` / `coverage` / `ranking-decrease` / `ranking-lb` /
`ranking-proc-decrease`).  Each kind has different verification
needs.  The SMT path treats them uniformly; a hybrid wouldn't
have to.

**Effort sketch.** Large — depends on Lean integration being
prerequisites (`RESEARCH.md` §B foundations).  But the
*dispatch* layer is small once both backends exist.

**Status.** Draft.  Premature until §B has a prototype.  Worth
noting as a structural refinement when we get there.

---

## P5 — Cover-benchmark inference from constraint-emission diff

**Idea.** Today's cover benchmarks (`cover_loop_branched_recur`,
`cover_chain_branched_recur`) were hand-crafted after the bug was
found.  Automate this: when the constraint-emission code changes,
diff the set of (context, constraint-kind) tuples emitted on each
existing benchmark against the previous version.  If a kind that
USED to be emitted in some context isn't anymore, generate (or
prompt for) a cover benchmark for that gap.

**Why it's interesting.** Lesson #27 says emission gaps come back
in different contexts.  We discovered #26 (SB-in-Loop-body
coverage missing), wrote a cover benchmark for it.  Discovered
#27's broader pattern, wrote another.  Each fix surfaces one
gap; an automated diff would surface them ALL at the time of the
constraint-emission refactor, before any benchmark flakes.

**What suggested it.** The structural refactor in Phase 5.B++
(extract `emit_sb_constraints`, `emit_loop_body`, etc.) was
exactly the moment when emission contracts changed.  Diffing
"what got emitted for every benchmark" before and after the
refactor would have flagged the SB-branch-recur and generator-
exhaustion gaps automatically.

**Effort sketch.** Medium.  Need a "emit constraint kinds and
their (context, hole_id) tuples" pass over the constraint
generator that doesn't actually call Z3.  Diff that pass's output
across git revisions.  A few days for a useful prototype.

**Status.** Draft.  Aligned with the user's bit-rot-prevention
concern.  Worth doing alongside CI setup (next step on the
plan).

---

## P6 — "Edge of feasibility" benchmark generator

**Idea.** The user's plan calls for scaling the benchmark suite
"until we get to the edge of feasibility".  Automate the
boundary-finding: for each benchmark, parametrize the *size* of
the predicate space (number of τ atoms, depth of quantifier
nesting, magnitude of bilinear coefficients) and run the
synthesizer with increasing size.  The largest size at which it
still completes in budget is the empirical feasibility frontier.
Track this over time as the synthesizer improves.

**Why it's interesting.** Right now we have qualitative
statements ("τ_inner with 7 quantified atoms hung past 7
minutes; trimmed to 4, works in 0.2s").  Quantitative frontier
data would tell us:
  - Which optimizations move the needle (Phase 3.L
    monotonicity-aware: how much did it shift the τ-atom-count
    frontier?).
  - Where to target the next optimization (if quantifier-instantiation
    cost dominates at the frontier, that's the bottleneck).
  - Whether the §A LLM-driver loop is even feasible at realistic
    benchmark scales.

**What suggested it.** The user's framing: "increase the tests
to MANY more cases until we get to the edge of feasibility."
This is already on the implicit roadmap; making it quantitative
makes it actionable.

**Effort sketch.** Medium-large.  A few days to set up the
parameterized benchmarks and the boundary-finding harness.
Ongoing cost to keep the frontier data fresh, but cheap if
integrated with CI.

**Status.** Draft.  This is what the user means by "edge of
feasibility" testing; an explicit frontier graph would be useful
output.

---

## P7 — Helper-citation codegen as structural plumbing (VALIDATED)

**Idea.** Replace the generic Lean tactic chain with a one-line
`exact <helper> <args>` citation when a Tier-3 helper matches the
obligation's chosen-atom subset.  Helpers carry the math (hand-
proven in `Helpers.lean`); codegen carries structural plumbing
only (signature derivation + citation glue).  Per-call cost drops
30-60s → ~2-5s for matching subsets.

**Why it's interesting.** The user had earlier rejected "codegen
as semantic proof writer" as driver-LLM territory.  But the
boundary turned out to be subtler: codegen-as-PLUMBING (the same
plumbing the translator already does when emitting `.failed.lean`
dumps, just citing a helper instead of trying a tactic chain) is
purely mechanical and NOT what the rejection covered.  The Tier-3
helper bodies are still human/LLM-authored math — codegen never
touches them.

**What suggested it.** Floyd-Warshall's bundle-post obligation
took 30-60s per generic-chain dispatch; with ~70 enumerated
subsets, total wall time blew past 30 minutes.  A single hand-
written helper proved the obligation for the full-τ case;
generalizing to "every superset of the helper's required atoms
hits the fast path" was the unlock.

**Status.** VALIDATED 2026-05-19.  Phase 1 (FW canary):
`floyd_warshall_post_from_inv` cited in 4.5s.  Phase 2 (corpus
ports): kadane / majority / modular_exp all synthesize E2E:

  | Bench                    | Pre-codegen     | Post-codegen | Speedup |
  | ---                      | ---             | ---          | ---     |
  | `kadane_max_subarray`    | 600s timeout    | **70s**      | 8.5×    |
  | `modular_exponentiation` | 1800s timeout   | **70s**      | 25×     |
  | `majority_element`       | UNSAT (1487s)   | **3min**     | works   |

Promoted to `RESEARCH.md §H.2.CODEGEN` with the full design +
validation findings (Lessons #45-#50).  See CLAUDE.md for the
implementation log.

**What was learned in validation that wasn't in the original
proposal**:

  - **`ranking-*` on Lean dispatch causes process-contention
    blowup**.  An exploratory routing change put ranking-* on
    the Lean path along with safety-*; kadane / modexp each
    regressed to 10-min timeouts.  Lean dispatch spawns
    `lake env lean` per call; for linear-arith obligations Z3
    handles in milliseconds, the overhead is fatal.  Reverted;
    `_AXIOM_HEAVY_DISPATCH_KINDS` is strictly safety-* + coverage.
  - **Coverage routing through Lean**.  Originally not in scope
    — coverage was Z3-only.  Validation surfaced that
    quantified-UF-axiom coverage constraints return spurious
    Z3 UNKNOWN; added `theorem_for_coverage` and routed.
  - **Helper short-circuit emits full τ, not minimal τ**.  Sound
    by construction (no over-generalization) but trades score-
    minimization.  Per-atom helpers (task #170) would restore
    minimization; deferred as not on the critical path.
  - **Cross-check selectivity**: `_on_z3_sat` must skip
    `ranking-*` (the spurious-UNKNOWN problem applies in
    reverse — Z3 SAT cross-check on empty-τ ranking returns
    spurious errors).

---

## Promotion process

When an idea here matures (concrete enough to act on, with a
clear scope and an owner), promote it to `RESEARCH.md` proper —
either as a new section or as a sub-thread under §A / §B / §C.
Edit the entry's **Status** to `promoted to RESEARCH.md` and
leave a one-line pointer.  Keep the draft entry here for
historical record.
