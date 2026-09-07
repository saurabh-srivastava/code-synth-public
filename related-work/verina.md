# Related work: VERINA (first-pass comparison)

**Paper:** *VERINA: Benchmarking Verifiable Code Generation*
(arXiv:2505.23135).
**This doc:** a first-pass read of VERINA and an honest
comparison against this repo's synthesizer.  Written to
find where the two artifacts genuinely differ, where a
head-to-head number would be misleading, and what VERINA
exposes about our own approach.

Status: first pass.  We have **not** yet run our
synthesizer on VERINA's tasks — that experiment is the main
actionable outcome (see §7).

---

## 1. What VERINA is

A **benchmark dataset**, not a tool or a synthesis system.
189 manually-curated verifiable-coding tasks in Lean 4,
split into two tiers:

| Subset          | Tasks | Source                                    | Max LoC (code/spec) |
| ---             | ---   | ---                                       | ---                 |
| VERINA-basic    | 108   | MBPP-DFY-50 (49 translated) + CloverBench (59) | 26 / 17        |
| VERINA-adv      | 81    | LeetCode, LiveCodeBench, course submissions    | 38 / 62        |

Each task bundles **five** components:
1. Natural-language description (~110-word median).
2. Lean 4 function signature.
3. Formal specification: a **precondition** `P` and
   **postcondition** `Q`, written as Lean predicates.
4. Reference implementation (ground-truth Lean 4 code).
5. Test suite: positive + negative tests, 100% line
   coverage.  (Ground-truth proofs are optional and not
   required for evaluation.)

It measures three **separately-scored** subtasks:
- **CodeGen** — generate code; scored `pass@k` on the
  positive tests via Lean `#guard`.
- **SpecGen** — generate the pre/postcondition; scored for
  soundness + completeness by a novel **test-based** check
  (`decide` + `plausible` property testing over concrete
  test values, rather than proving the universally
  quantified implication).
- **ProofGen** — generate a Lean proof that the code meets
  the spec; scored by the Lean compiler (any `sorry` =
  fail).  **No SMT / hammer / tactic automation** — the LLM
  writes the Lean proof directly.

### Headline results (best models)

| Metric   | o4-mini pass@1 | with 64× refinement            |
| ---      | ---            | ---                            |
| CodeGen  | 61.4%          | —                              |
| SpecGen  | 51.0%          | —                              |
| ProofGen | **3.6%**       | 22.2% (basic) / 6.17% (adv)    |

(The abstract also quotes o3 at 72.6% / 52.3% / 4.9% on a
slightly different cut. Either way: proof generation is the
wall.)  The paper's own framing: constructing Lean proofs
that an implementation satisfies its spec is "particularly
hard and requires specialized theorem-proving
capabilities."

---

## 2. What our system is

A **synthesis system** (a tool), not a benchmark.  Lineage:
POPL'10 proof-theoretic synthesis over predicate
abstraction + PLDI'11 + the PLDI'09 attribute-class
reduction.

Input: a `Problem` = (control-flow **template**, a
**predicate space** of candidate atoms per hole, a **spec**
as pre/post strings + optional uninterpreted-function
axioms).

Output: `(code, proof)` — the synthesized program plus a
**discovered inductive invariant + termination-ranking
function**, with every proof obligation discharged by a
**dual verifier**: Z3 (primary SMT) and Lean 4 (for
axiom-heavy obligations Z3 can't decide, via curated
`.solved.lean` companions cached by signature hash).  Code
is emitted to Python, C, or Rust.

**Sound by default**: a solution is returned only if every
obligation is Z3-VALID or Lean-VALID.  No unverified code
is ever emitted.

Scale: 90 in-repo benchmarks + 25 agent-authored via the
community-validation rounds.

---

## 3. The core architectural difference

This is the whole comparison in one line:

> **VERINA treats proof as a generation task.  We treat
> proof as a search task.**

VERINA's pipeline (generate-then-check):

```
NL + signature + spec  ──LLM──▶  Lean proof  ──Lean kernel──▶  3.6% pass
                                 (given the reference code)
```

Our pipeline (search / correct-by-construction):

```
NL ──LLM──▶ (template + predicate space + spec + UF axioms)
   ──constraint solver over attribute classes (Z3 + Lean)──▶
   (code + invariant + ranking + proof)
   [emitted only if every obligation verifies]
```

The 3.6% ProofGen number is essentially *"how good are LLMs
at writing Lean tactic scripts"* — which is exactly the
step our pipeline **does not perform**.  We never ask a
model to write a proof.  The invariant, the ranking
function, and the discharge of each obligation fall out of
the constraint search; Lean/Z3 only *check* small,
mechanically-generated obligations (often one-liners like
`omega` or `exact (user_axiom_0 args).symm`).  This is the
original POPL'10 thesis: don't generate proofs, search for
proof-carrying programs.

So on the specific axis VERINA identifies as the wall
(LLM-authored Lean proofs), our architecture sidesteps the
wall rather than climbing it.

---

## 4. Head-to-head (with the asymmetries marked)

| Dimension | VERINA (o4-mini) | This repo |
| --- | --- | --- |
| Artifact type | benchmark/dataset | synthesis tool |
| Who writes the code | LLM (or given) | **synthesizer searches** |
| Who writes the proof | **LLM writes Lean tactics** | **solver + SMT/Lean discharge** |
| Proof automation | none (kernel check only) | Z3 + Lean, cached companions |
| Verified-output rate | 3.6% pass@1 proof | 100% (sound by construction) † |
| Code is… | proved *as given* | **chosen to be provable** † |
| Spec provenance | benchmark-fixed | human/LLM-authored per problem † |
| Human scaffolding / problem | low (end-to-end LLM) | high (template + predicate space) † |
| External held-out eval | yes (189 curated tasks) | **no** † |

† = the asymmetries that make a raw number comparison
misleading.  See §5.

---

## 5. Why a direct number comparison would be dishonest

Our "100% verified" and VERINA's "3.6% proof" are **not**
the same measurement.  Four reasons, in decreasing order of
how much they matter:

1. **We synthesize code to be provable; VERINA proves given
   code.**  VERINA hands the model a fixed reference
   implementation and asks it to prove *that specific code*.
   We get to emit only code our system can already prove —
   we never face an adversarially-given implementation.
   This is the single biggest asymmetry.

2. **Our benchmarks are self-authored; VERINA's are
   externally curated.**  Our 100%-verified rounds (v5–v9)
   were on problems where *we* picked the difficulty, the
   template, and the predicate space.  VERINA's 189 tasks
   are a standardized held-out set spanning MBPP/LeetCode.
   We have never scored on an external held-out set.

3. **We assume the spec; VERINA measures it.**  VERINA's
   SpecGen metric (51% sound+complete even for the best
   model) quantifies something we currently take on trust:
   whether the written spec actually captures intent.  In
   our trust surface (see `END-TO-END.md` §6), the spec is
   an *axiom* the reviewer must accept.  "Provably correct"
   in our system means "provably correct **w.r.t. a spec
   that may itself be unsound or incomplete**."

4. **Autonomy vs. reliability tradeoff.**  VERINA's setup
   is more autonomous (LLM does NL→code→spec→proof end to
   end) and fails at the proof step.  Ours is more reliable
   but needs more scaffolding per problem (a control-flow
   template and a predicate space, hand- or LLM-authored).
   Different points on the same frontier, not the same
   contest.

---

## 6. What VERINA exposes about *our* approach

Reading VERINA is most valuable as a mirror:

- **We are missing an external benchmark.** Every
  correctness claim we've made is on self-authored
  problems.  VERINA-basic (108 tasks, MBPP-derived) is
  exactly the kind of held-out set that would turn our
  "100% on our own benchmarks" into a defensible external
  number — or expose where we fall over.

- **Our spec-trust gap is real and now quantified.**
  VERINA shows even frontier LLMs write unsound/incomplete
  specs ~half the time.  Our pipeline inherits that risk
  wholesale and doesn't measure it.  Adopting VERINA's
  test-based SpecGen check (`decide` + `plausible` over
  concrete tests) would let us report spec quality as a
  first-class number instead of hiding it in the trust
  surface.

- **Their proof bottleneck validates our design bet.**  The
  independent finding that LLM-authored Lean proofs top out
  at single digits is direct third-party evidence for the
  proof-as-search architecture.  Worth citing in the paper
  / thread as external corroboration.

---

## 7. Actionable: run our synthesizer on VERINA-basic

The honest next step is not to claim a win — it's to run
the experiment:

1. **Port VERINA-basic's 108 tasks** into `Problem` objects
   (NL description → template + predicate space + pre/post;
   the pre/post are already Lean predicates, so translation
   to our spec strings is mostly mechanical).
2. **Report three honest numbers**:
   - How many we can synthesize + verify at all.
   - How many need a hand-authored template vs. an
     LLM-guessed one (measures the scaffolding cost from
     §5.4).
   - Wall-clock + trust surface per task.
3. **Adopt VERINA's SpecGen check** on the specs we
   consume, so we can state spec soundness/completeness for
   our own corpus.
4. Any task we *cannot* express (no finite predicate space,
   non-loop control flow, higher-order spec) is itself a
   finding about the reach of proof-theoretic synthesis vs.
   general LLM code-gen.

The comparison that would actually mean something:
**"of VERINA-basic's 108 tasks, our synthesizer produces a
verified (code, proof) for N, with template hand-authored
for M of them"** — reported next to VERINA's 22.2% refined
proof rate on the same tasks.

---

## 8. First-pass verdict

VERINA and this repo are **complementary, not
competitors**: VERINA is the evaluation instrument; we are
a system that should be evaluated on it.

The one substantive architectural claim that survives
scrutiny: **by searching for proof-carrying programs
instead of generating proofs, we avoid the exact step
(LLM-writes-Lean-tactics) that VERINA measures as the
field's current wall.**  Everything beyond that — any claim
about relative success rates — is unearned until we run our
system on their tasks (§7).  Until then, treat VERINA as
the held-out benchmark we've been missing, and its SpecGen
metric as a gap in our own trust story.
