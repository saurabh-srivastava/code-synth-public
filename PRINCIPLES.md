# PRINCIPLES.md

Operational always-on reminders, governing principles, and
north-star expansions for the project.  Referenced from
`CLAUDE.md`, `problem.skill`, and `debug.skill`.

When something here gets banked as a new principle, update
this doc first; the three referencing docs each carry a
short pointer or a 1-paragraph summary, not the full
content.

---

## North-star expansions

The project's three long-horizon north stars are introduced
in `README.md`.  This section captures the *implementer-
facing* expansion of each.

### NS-1.  Resource-bounded synthesis (correctness + termination → +runtime +space)

Extend the proof obligation from `(partial correctness ∧
termination)` to additionally cover worst-case time and
space complexity.

> **Status (2026-05-22): substrate landed.**  See
> `COST_INVS.md` for the full slice-by-slice design and
> `CHANGELOG.md` for what shipped.  Six cost-bound corpus
> benchmarks (`benchmarks/cost_invs/...`) + one cost-bound
> graph-flavored benchmark
> (`benchmarks/open_prbs/l16_bipartite_matching/
> bench_glover_verify.py`) synthesize end-to-end.  Real
> algorithm discovery on graph problems still needs a
> graph IR + list/array primitives + new operations —
> multi-week future work.

#### NS-1.1 The PLDI'09 substrate is most of the way there

PLDI'09's "templates over predicate abstraction" reduction
generalizes naturally to RESOURCE templates: cost variables
get hole positions just like τ atoms, and recurrence axioms
over those variables (e.g. `T(n) ≤ 2T(n/2) + O(n)`) get
supplied like `user_axiom_*` are today.

What's needed in the IR:
- `cost@<loop_id>` and `cost@<recur_id>` holes carrying
  candidate resource expressions (analog of `phi@`).
- Per-loop / per-recur cost recurrence axioms.
- A "cost-asserting" Pre/Post extension: `pre`, `post`,
  `pre_cost`, `post_cost`, plus a `cost_bound` spec.
- Decoder emits a third proof annotation: `cost L0: ...`
  alongside `invariant` and `ranking`.

#### NS-1.2 Why this is post-Phase Y, not in parallel

- Resource bounds require Pre/Post that mention `O(...)` or
  closed forms — these are syntactic extensions to the spec
  language that need design.
- Most useful with the LLM driver in place — the driver can
  propose `cost_bound = O(n^2)` from "this should be quadratic"
  English, and iterate.
- The corpus from Phase X provides ground truth: each existing
  `Problem` has a known worst-case complexity; annotating them
  builds the resource-template predicate space.

#### NS-1.3 Open questions

- **Symbolic cost (LIA over n) vs Big-O comparison.**
  Z3 handles the former; the latter requires Lean / a
  custom comparator.
- **Amortized analysis.**  PLDI'09 mostly addressed
  worst-case per-operation.  Amortized bounds (potential-
  method style) layer on but need their own template
  structure.
- **Branch-specific cost.**  When a branch has higher cost
  than another, ranking-function-style ϕ for the cost
  variable bounds the dominant branch.

### NS-2.  Module-level synthesis (assume-guarantee)

Lift the unit of synthesis from a single function (one
`Problem`) to a full multi-function program.

#### NS-2.1 Shape

A `Module` consumes:
- An English description of the module's responsibility.
- Optional interface hints (what functions the module
  exports).

It produces:
- One or more synthesized functions.
- Their interfaces (signatures + contracts).
- A composed proof: each function correct against its
  contract; the module's top-level entry point correct
  against the module's external spec.

Internal calls between functions verify against the
callee's contract (assumed) rather than its body.  This is
the standard **assume-guarantee** decomposition: each
function's proof is local; composition is by
contract-matching.

#### NS-2.2 What today already supports

`Problem.uninterpreted` + `Problem.axioms` are the
substrate.  A callee with a known contract becomes an
uninterpreted function plus axioms encoding its contract.
Outer-function synthesis verifies against those axioms.
Then the callee's body is synthesized as a separate
`Problem` whose Pre/Post matches the contract.

The gap is INTERFACE SYNTHESIS: choosing what functions to
factor out, with what signatures, with what contracts.
Today the user pre-specifies the contracts (via UFs /
axioms); the target is for the LLM driver to propose them.

#### NS-2.3 Open questions

- **Interface proposal.**  How does the LLM choose where to
  factor out a sub-function?  The same template /
  predicate-space intuition applies: a *module template*
  (a graph of function slots with edges = call
  relationships) covers a search space of decompositions.
- **Contract refinement loop.**  When the outer function
  fails to synthesize against the proposed contracts, the
  LLM weakens / strengthens contracts and retries.
- **Recursive modules.**  Self-calls between functions in a
  module need fixpoint reasoning — the same vacuous-Fpre /
  ranking machinery as Phase 3.E generalized.

### NS-3.  Novel program discovery

The synthesizer's primary value isn't reproducing known
programs — it's discovering programs that **solve a stated
English problem optimally under a resource bound**, where
the realization may not be in any textbook.

#### NS-3.1 Existing evidence

POPL'10's Strassen template ranged over 2×2 matrix
multiplication algorithms; the published-canonical Strassen
is one realization, but the synthesizer surfaced OTHERS
with the same 7-multiplication property — provably correct,
provably optimal-cost, NOT in the literature.

#### NS-3.2 Operating mode (target)

```
Input:
  - English spec (e.g., "multiply two n×n matrices")
  - Resource bound (e.g., "with fewer than 2.81 mults/element")

Search over:
  - Templates (acyclic / loop / recursive shapes consistent
    with the resource bound).
  - Predicate spaces (linear combinations of input entries).
  - Cost recurrences (giving the resource bound a closed
    form).

Output:
  - A program (perhaps novel) that meets the bound, with
    correctness + termination + resource proofs.
```

#### NS-3.3 Dependencies and sequencing

- Requires **NS-1** (resource-bounded synthesis).  Without
  cost proofs, "novel + optimal" isn't a verifiable claim.
- Requires **NS-2** indirectly: many novel algorithms
  decompose through unfamiliar interfaces.
- Requires the **LLM driver from `NL_FRONTEND.md`** to be
  strong at proposing template + predicate spaces.

#### NS-3.4 Open questions

- **Search space size.**  Pareto-frontier exploration is
  the natural framing.
- **Equivalence classes.**  Two superficially-different
  realizations may be algebraically equivalent.
  Canonicalizing before claiming "novel" needs a
  normalization story.
- **Publishability.**  Each discovered novel algorithm is a
  small paper.

#### NS-3.5 IR extensions required for true discovery

Phase X.S surfaced a concrete gap.  `strassen_3x3_laderman`
VERIFIED Laderman's known 23-product algorithm; the companion
`strassen_3x3_lt23mult_search.py` attempted a 22-product search
by hand-crafting 23 candidates (each dropping one of Laderman's
products).  All correctly rejected — confirming the
synthesizer's discrimination — but the experiment exposed that
**our current IR can only search OVER user-specified candidate
transitions**, not OVER a parameterized template space.

For real discovery (e.g., finding a 22-product 3x3 matmul
algorithm if one exists), the IR needs one of:

1. **Parametric m_i templates** — each m_i specified as
   `(linear combination of a's with coefficient holes) ×
   (linear combination of b's with coefficient holes)`, where
   the holes draw from a small symbolic search space (e.g.,
   `{-1, 0, 1}` for tractable enumeration, or symbolic for
   richer search).  The synthesizer would then search the
   Cartesian product of all coefficient choices across all m_i
   slots, with structural constraints (e.g., "at most 22
   non-trivial products").  This is the natural extension of
   the current SSA-list candidate atom format — each "atom"
   becomes a TEMPLATE with holes rather than a concrete chain.

2. **Lifting to a richer search domain** — algebraic-geometry
   methods (Gröbner bases over the polynomial ideal),
   tensor-decomposition libraries (e.g., AlphaTensor-style RL
   policies, Smirnov's approximate-rank tools), or hand-rolled
   SMT encodings of the bilinear-rank constraints.  This goes
   beyond the SMT-driven attribute-class reduction PLDI'09
   provides; it likely requires a separate "discovery backend"
   beside the existing Z3 / Lean verifier.

Both extensions are post-Phase-Y in sequencing: the driver-LLM
should be the first searcher of templates, and we need to know
how it performs on KNOWN templates (Phase Y.1) before
investing in either extension.  Track these as Phase Z' or
later, gated on a benchmark that's demonstrably bottlenecked
on the current "user-specified candidate" limitation.

The `lt23mult_search.py` benchmark serves as a permanent
research data point: a discrimination test today, a "this is
what the discovery extension needs to be able to search" target
for tomorrow.

---

## Governing principles

### P-1.  Framework improvements over single-case fixes

> **Given the choice between solving for a single case vs
> improving the general framework, always opt for the
> latter.**

The project's value lives in the framework, not the
benchmarks.  Each benchmark validates ONE point in
capability space; each framework primitive expands the
ADMISSIBLE capability space.  A workaround that lets one
benchmark close adds +1 to "benchmarks done."  A framework
primitive that closes that benchmark cleanly AND enables 10
future benchmarks adds +11.  Linear vs compounding work.

**Estimation heuristic.**  When you encounter a framework
gap, estimate three things:

- **(a)** Time to author a one-off workaround.
- **(b)** Time to author the framework primitive + use it
  cleanly.
- **(c)** Number of future benchmarks / algorithms that
  the primitive would unblock.

Choose the framework path unless (c) is clearly 0–1 AND
(b) has substantial design risk.  When in doubt, prefer
the framework.

**Counter-examples** (when the principle does NOT apply):
- Pure benchmark-content issues (wrong τ atom, missing
  axiom, initialization that violates the pre).
- Helper authoring for existing primitives — author the
  `.solved.lean` helper.  Don't extend the framework to
  make `aesop` smarter.
- Cosmetic decoder/emitter output.

**Concrete cases this paid back**: Slice C harness over
unified-SAT `TemplateUnion`; K.A.3 lambda-bound vars typed
by name suffix; K.3.2 `break` primitive over
`made_progress` flag.  See `CHANGELOG.md` for the full
L1.6 arc.

#### P-1 case study: the L1.6 thread

The L1.6 arc (Slice A → B → C → C1.A-C → C1.D) is a
progression where framework extensions repeatedly paid back:

  - **Slice A** identified multi-candidate via UFs.  This
    was already an existing framework feature.
  - **Slice B** dropped to concrete operations.  No
    framework changes; just better atom-space design.
  - **Slice B.3** added `int[][]` to emit_c and emit_rust —
    framework change; unblocked matching benchmarks
    compiling to real source.
  - **Slice C** added the `multi_template_solve` harness —
    framework primitive.
  - **C1.D K.A.3** added lambda-suffix typing — framework
    extension.
  - **C1.D K.3.2** added `break` — framework primitive.

If we had taken single-case workarounds at each step, we'd
have 6 benchmark-specific kludges and no reusable
infrastructure.  Instead each step left the framework
strictly more capable, with the next benchmark cheaper to
author than the last.

### P-2.  Axiom-free preferred (Tier-1 over Tier-2) — even at extra cost

When a Tier-3 helper has a choice between "axiomatize the
preservation claim" (3-line Tier-2 axiom) vs. "prove the
preservation from concrete state semantics + step axioms"
(50-200 LOC Tier-1 theorem), **DEFAULT to the Tier-1 proof
path**.  Each axiom we displace is a concrete
trust-reduction win that compounds across every future
benchmark sharing the same proof pattern.

**Why**: the project's headline claim is "synthesized
algorithms come with formal proofs."  Each Tier-2 axiom is
a CRACK in that claim — a place where the user has to
trust prose-level reasoning instead of mechanically-checked
Lean.

**How to apply**: when authoring a new helper, first stand
it up as Tier-2 (axiom) per the two-phase workflow in
`problem.skill` — get the E2E synth closing.  THEN, before
declaring the benchmark "done," budget a focused session
to promote each load-bearing axiom to a Tier-1 theorem.

**Acceptable Tier-2 axioms**:
- (a) Genuinely-classical theorems whose proof is multi-day
  Lean work (Berge's theorem; GS stability).
- (b) Recursive-UF base + step axioms that DEFINE the UF's
  semantics (e.g., `gs_base_mate`, `gs_accept_mate_at_mm`
  — these are not "facts we trust" but "the UF's recursive
  definition").

All other axioms should be promoted.

**Validated by**: Slice 2.B (5 axioms) → Slice 2.C (2 axioms,
~120 LOC `flip_preserves_im` proof); GS Phase 3 (0
algorithm-preservation axioms; 6 Tier-1 helpers including
~170 LOC ACCEPT proof).  Lessons #76.

**Counter-example case**: don't pre-emptively promote an
axiom on a benchmark that doesn't yet synthesize.  Tier-2-
first as DEFENSE against wasted proof effort; Tier-1-
promotion-before-shipping as ALIGNMENT with the project's
trust claim.

### P-3.  Dummy axiom `["0 == 0"]` to force axiom-heavy Lean dispatch

Any benchmark whose pre / post / τ contains *quantified*
atoms over array-typed state (e.g., `ForAll(lambda k: ...
M[k] ...)`, matching-invariants, sortedness predicates)
should set `axioms = ["0 == 0"]` even when no real axioms
are needed.

**Why**: with `axioms = []` and `uninterpreted = []`, the
framework routes safety obligations to Z3 first.  Z3's
quantifier-instantiation heuristics are *unreliable* on
quantified-array atoms — spurious SAT (false invalid) or
UNKNOWN.  Either way, the per-class enumeration produces a
corrupt validity table.

The dummy `"0 == 0"` axiom satisfies the framework's
`bool(problem.axioms)` check that gates the axiom-heavy
dispatch path.  Under that path, safety obligations route
through Lean directly.

**Cost**: ~5–30× wall-clock per safety obligation (Lean
dispatches are 4–15s vs Z3's milliseconds).  But sound >
fast.

**Counter-example case** (when NOT to use): pure-int /
linear-arithmetic benchmarks where Z3 is reliable.
`intsqrt`, `sumi`, `intdiv`, the `COST_INVS` arithmetic
benchmarks — all stay on Z3 dispatch.

**Validated by**: B.1 `bench_pair_consecutive`, B.2
`bench_pair_multi_count`, B.4 `bench_glover_concrete`,
Slice C `bench_l16_multi_template`, C1.A-C
`bench_greedy_match_general`, C1.D K.3.2
`bench_aug3_inner_search`.  Every L1.6 concrete-matching
benchmark uses this trick.  Lesson #65.

### P-4.  Lean axiomatize + Z3 shim, not pure Z3 SAT past the wedge limit

For open-problem exploration (`open_prbs/`), the default
approach is library-axiomatized structural-class
speculation searched via Z3 — NOT a direct Z3 SAT encoding
over the full search space.  Pattern: identify
sub-algorithms that can be axiomatized as Lean library
entries; let Z3 search the small parametric residual on
top.

**Why**: the framework's confirmed reach is ~200-300
search vars for hard Z3 SAT.  Past that, Z3 wedges (L2.1
n=5 polymul; L1.2 K=10 direct SAT; L1.5 threshold-35;
L3.1 sorting nets at N≥7; L3.4 joint encoder at K-S 12).
Pure-Boolean SAT shapes also wedge Z3.  But Z3 *with*
Lean-axiomatized building blocks remains tractable.

**How to apply**: before writing a direct Z3 encoding for
an open problem, ask first — *what can be axiomatized?*
If the answer is "nothing," warn that direct search will
likely wedge.  For genuinely-open frontier problems, the
deliverable should be a comprehensive structural-class
narrative (sweep over library-axiomatized speculations),
NOT a successful direct search.

---

## Always-on reminders for the implementer

### A-1.  Iterate non-trivial Lean proofs in scratch first

When converting a Tier-2 axiom to a Tier-1 theorem and the
proof is more than ~10 lines (e.g., involves `store2d`
case-splits, multiple `subst`s, `simp [user_axiom_*]`
chains), write the proof in a SCRATCH `.lean` file first:

1. Copy the axiom signature into a temp file (e.g.,
   `scratch/<benchmark>_proof_attempt.lean`).  Import
   `SynthLean.Basic` + the relevant `Helpers` module so the
   user_axioms are in scope.
2. Iterate the proof there with `lake env lean <file>` until
   it closes.  Each `subst` direction, `⟨...⟩` inference,
   and pattern match failure surfaces fast without breaking
   the canonical `Helpers.lean`.
3. Once the proof closes in scratch, port it into the
   canonical file.  Rebuild Helpers; smoke-test that
   `verify_class_via_lean` still validates via the cite.

Symptoms that indicate "scratch first": (a) multiple
conjuncts where omega/nlinarith aren't enough, (b) any use
of `simp [store2d]` with `if_pos` / `if_neg`, (c) `subst`
over multiple frame equations, (d) needing rewrites that
involve `user_axiom_*` applications with computed arguments.

### A-2.  Tier-2-first authoring workflow for new helpers

**Path choice (community-validation finding F4,
2026-06-08)**: for FIRST-TIME authoring, prefer
**`.solved.lean` companions** over `HelperRegistry`:

- **`.solved.lean` companions** are file-path-resolved cache
  entries (`<dump_dir>/<stem>.solved.lean` next to the
  `<stem>.failed.lean` the synth emits).  No
  `lean/SynthLean.lean` import required; bypasses the
  Lean-dispatch cold-cache trap via signature-hash cache
  lookup.
- **`HelperRegistry` + `Helpers.lean`** is cleaner when
  multiple benchmarks share the same proof shape — and is
  required by some advanced features (e.g., per-helper
  `required_atoms` gating).  But it requires (a) adding an
  import to `lean/SynthLean.lean`, (b) `lake build` of the
  helper module, (c) the dispatch path being warm.  The
  community-validation test surfaced (a) and (c) as
  repeated stumbling blocks.

**Default**: ship `.solved.lean` first; promote to
`HelperRegistry` when ≥2 benchmarks share a proof shape.

When a benchmark needs a Tier-3 helper, follow this
two-phase workflow:

1. **Axiomatize first.**  Write the helper as an `axiom` in
   `Helpers.lean` with the translator's emitted signature.
   Wire the cite + `HelperEntry`.  Smoke-test
   `verify_class_via_lean` to confirm the citation
   type-checks.  Run E2E to confirm the benchmark
   synthesizes.  This decouples "does the helper short-
   circuit work end-to-end" from "is the math actually
   provable."
2. **Prove the theorem second.**  Promote the `axiom` to a
   `theorem` with an explicit proof (per P-2 above).
   Build to confirm Lean accepts the proof; re-smoke-test
   `verify_class_via_lean` to confirm helper=True still
   fires.  The axiom is gone; trust is now from a proof.

The two-phase workflow avoids two failure modes: (a)
wasting proof-engineering effort on a helper whose citation
doesn't even type-check (translator-vs-axiom binder
mismatch); and (b) shipping a benchmark "verified" via an
unprovable axiom.

### A-3.  Runtime budget: target <10s wall-clock per benchmark

Most corpus benchmarks should synthesize verified solutions
in under 10 seconds.  When a benchmark consistently exceeds
this (visible via the `[SLOW: Nx baseline]` annotation in
`tests/regression.py`, or just a long elapsed time on a solo
synth run), investigate before accepting:

- Does it need a Tier-2 axiom helper to short-circuit
  enumeration?
- Is the τ space too large?  Consider whether all atoms are
  load-bearing.
- Is cardinality-ordered enum applicable (ANT-only τ ≥ 10
  atoms in a `ranking-*` obligation)?  See `SOUNDNESS.md`.

Slow benchmarks are diagnostic signals, not acceptable
cost.  Update `tests/regression_timings.json` when
intentional changes shift a baseline.

### A-4.  Session-transcript rotation

Every so often (rough heuristic: when the working session
has grown long enough that scrolling back is painful, OR
roughly every 5-10 substantive commits), the project owner
runs `/export` and stashes the file under
`dev-transcripts/<short-sha>.md`.  Once a transcript
file is in that directory, it should be committed alongside
other work — transcripts are part of the project's history
and decision trail.

---

## Project conventions

- The user is the first author of both papers.  Use their
  terminology (scaffold, transition system, Dprf, Πp/Πe,
  VS3-PA).  Don't re-explain the basics; do ask theory
  questions when stuck.
- The PINS C# source in `ref/pins-src/` is a cross-check
  for algorithm details, **not** a template for our API or
  surface choices.  We are not copying its annotated-C +
  macros design.
- Python tooling goes in a project-local `.venv`, not
  Homebrew or system pip.
