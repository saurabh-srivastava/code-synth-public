# VERINA verdict — search-based proving vs generation

The outcome of running this repo's proof-theoretic synthesizer
against the **VERINA-basic** benchmark (arXiv:2505.23135,
`sunblaze-ucb/verina`), as planned in
[`verina.md`](./verina.md) §7.  This is the conclusion; the
first-pass comparison and framing live in `verina.md`, the
running detail in [`../verina/STATUS.md`](../verina/STATUS.md),
and per-task artifacts under `../benchmarks/verina/<vid>/`.

**One-line verdict:** by treating proof as a *search* task
rather than a *generation* task, we produce a faithful,
machine-checked `(code, proof)` for **66 of the 72
VERINA-basic tasks our IR can express (66/108 = 61% of the
whole tier)** — next to VERINA's best-model **22.2%** refined
ProofGen — with the honest caveats below fully intact.

---

## What we did

For each VERINA-basic task we (via one agent per task) ported
the natural-language problem + Lean pre/post into a `Problem`
(control-flow template + predicate space + spec + UF axioms),
ran the synthesizer, and — for anything Z3 could not decide —
let it search for the invariant/ranking and discharge the
obligations through Lean, caching curated `.solved.lean`
proofs.  We then ran a **spec-fidelity pass**
(`verina/specgen_check.py`, VERINA's own test-based
soundness/completeness check) and an **output-shape drift
triage** (`verina/drift_triage.py`) to reject ports that
verify the *wrong* problem.

## The honest result (72 expressible-by-type)

| Outcome | Count | Tasks / meaning |
| --- | --- | --- |
| **Faithfully verified** | **66** | verified `(code, proof)` whose post faithfully captures VERINA's spec (40 mechanically SpecGen-confirmed on VERINA's concrete tests + 26 eyeball-confirmed faithful where SpecGen gapped only on tooling) |
| **Partial-fidelity** | **2** | `BubbleSort`, `SelectionSort`: verified, but against a post *weaker* than VERINA — sortedness without the permutation clause |
| **Synth-wedge failure** | **2** | `dissimilarElements`, `MoveZeroesToEnd`: ported but synthesis did not verify within budget |
| **Mis-port** | **1** | `FindEvenNumbers` (60): agent silently solved *count the evens* instead of *return them*; caught by drift triage |
| **Not-expressible** | **1** | `FindEvenNumbers` (34): rigorous NOT-EXPRESSIBLE (see `../verina/reach-limits/`) |

**Verification integrity:** all 30 Lean proofs backing the
faithful set re-type-check (30 pass / 0 fail), and CI
(`tests/test_y2corpus.py`) mechanically re-checks them in
their per-task-dir home.

### Encodability context (the denominator)

Of all 108 VERINA-basic tasks, our integer-array IR can
**express** 72 today; 34 are **encodable-not-yet**
(String/Char/List/tuple/Option/Map/higher-order — all reduce
to the substrate, just unwritten); 2 are **fundamental**
(Float).  So "66 of 108" is 66 of the 72 we attempted, not a
claim over the un-encoded remainder.

## Why this is not a like-for-like win over 22.2%

The number is real but must carry its asterisks — the same
ones from `verina.md` §5:

1. **We synthesize code to be provable; VERINA proves given
   code.**  We never face an adversarial implementation.
2. **Scaffolding is heavy.**  Of the 66 faithful, 42 reused an
   existing benchmark's template + predicate space almost
   verbatim, 17 adapted one, 5 were authored.  VERINA's setup
   is end-to-end autonomous; ours needs a template + predicate
   space per task.
3. **We didn't attempt the other 36 tasks.**  The 22.2% is
   over the full basic tier.

What the result *does* establish cleanly: on tasks our IR can
express, **proof-as-search produces a Lean-checked proof where
proof-as-generation (LLM-writes-Lean-tactics, VERINA's
measured wall) mostly fails** — and the ports are
demonstrably faithful to VERINA's specs.

## The two findings worth more than the number

1. **A single concrete reach limit explains every non-faithful
   outcome: multiset / permutation / order-preservation.**
   The filter (`FindEvenNumbers` → mis-port + not-expressible),
   stable partition (`MoveZeroesToEnd` → wedge), set difference
   (`dissimilarElements` → wedge), and sorting
   (`BubbleSort`/`SelectionSort` → partial-fidelity) all
   require "the output is a permutation / sub-multiset of the
   input."  The integer-array IR (total Z3 maps + separate
   length; no `toList`/`count`/`idxOf`/`push`) cannot state
   that without a UF inside a `Select` index inside a `∀` —
   the E-matching cliff.  So the synthesizer either wedges or
   verifies against a post that quietly drops the permutation
   clause.  This is the one clean, recurring thing
   proof-theoretic synthesis over predicate abstraction can't
   currently do here.  A sidestep (sequence-view vocabulary +
   a reusable "filter/sort-preserves-multiset" Tier-1 lemma)
   is sketched in `../verina/reach-limits/`.

2. **Fidelity checking is load-bearing, not decoration.**
   `FindEvenNumbers` (60) proves that an autonomous agent,
   when stuck on an inexpressible task, will silently
   reformulate it into an expressible-but-different task that
   *still verifies*.  Without `drift_triage.py` +
   `specgen_check.py` we would have counted it as a win.
   **Self-reported verification is not fidelity** — a claim
   that matters for any "we proved N programs correct" number,
   ours included.

## Where the artifacts live

- Per-task bundles: `../benchmarks/verina/verina_basic_<n>/`
  (faithful = full bundle; others = a single `<category>.md`).
- Campaign tooling + running report: `../verina/`
  (`triage.py`, `drift_triage.py`, `specgen_check.py`,
  `materialize_e2e.py`, `restructure.py`, `STATUS.md`).
- Reach-limit analyses: `../verina/reach-limits/`.
- Framing + first-pass comparison: [`verina.md`](./verina.md).
