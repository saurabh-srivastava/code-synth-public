# NL_FRONTEND.md — Natural-language front-end via fine-tuned LLM

**Status (2026-06-07)**: parked design doc.  Not yet started;
will embark at a later time.  This doc captures the detailed
plan for *how* to build the NL front-end so future-us can pick
up without re-deriving.

**Pointer-in**: `RESEARCH.md §A` (the original NL front-end
thread).  This doc is the implementation deep-dive; §A
remains the conceptual framing.

**Pointer-out**: `problem.skill` and `debug.skill` are the
load-bearing reference material the FT'd LLM will read.

---

## Goal recap

An 8B–32B class LLM as the *proposer* in the synthesis loop:

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

The LLM is **untrusted** — the synthesizer's soundness gate
catches every wrong proposal.  The LLM only has to *propose
plausibly*, which is exactly the regime where a fine-tuned
8B-32B model is cost-effective.

---

## Data generation

### Seed (~60-80 examples — free)

Every existing verified benchmark has a `description = "..."`
field (the English spec a user would write) + the full
`Problem` record.  This is high-quality ground truth.  Free.

### Augmentation (~800-2000 examples — cheap)

Multiplies the seed by ~10×:

- **Paraphrase each `description`** via Claude / GPT-4 with
  prompts like "rewrite as a docstring," "rewrite as a
  one-liner," "rewrite as a multi-paragraph spec."  5-10
  paraphrases per benchmark.
- **Ablation variants**: same Problem with stripped/expanded
  pre, with different atom orderings, with extra distractor
  atoms (teaches "rejection").

### Synthetic (~30K-50K examples — the meat)

Teacher LLM generates candidate `(English, Problem)` pairs
from scratch given the `problem.skill` reference.  Validate
each by running `synth.solve()`:

- If verified → keep the pair.
- If failed → either discard OR include as a `(English,
  FailedProblem, repair_diagnostic)` example with the synth
  failure mode (these become failure-feedback training data).

Bias the generation toward shapes the synthesizer handles
well (single-loop arithmetic, recursive-UF, conditional
acyclic, the L1.6 / GS patterns).

Cost breakdown for 50K candidates:
- Teacher-LLM API: ~$0.01 per pair (Claude Haiku /
  GPT-4o-mini) → **~$500**; or ~$0.03 per pair (Claude
  Sonnet) → **~$1500**.
- Synth verification: free locally, but ~10-30s per
  candidate → 50K × 20s ≈ 11 days on 1 machine.  **Use the
  parallel synth-subprocess harness; 8-way → 1.4 days.**
- Expected discard rate: 20-40% (synth timeout, invalid
  templates, contradictory atoms).

### HumanEval-derived (~50-80 examples — high-quality)

The 47 GREEN problems from `HUMANEVAL.STATUS.md` can be
hand-authored once.  ~40-80 hours of curator time, but
yields the highest-quality "real-world spec" examples in
the dataset — these are out-of-distribution from the
project-internal benchmarks and will dominate the
evaluation set.

### Failure-feedback (~5K examples — load-bearing)

Each `(English, FailedProblem, RepairedProblem)` triple
teaches the model to read `NoSolution.hints` and adjust.
Generate by:

1. Take a verified `(English, Problem)` pair.
2. Deliberately corrupt the Problem (drop an atom, weaken
   a guard, mistype the post).
3. Run `synth.solve()` → record the failure verdict.
4. Triple is `(English, corrupted_Problem, failure_hints,
   original_Problem)`.

These pairs are **load-bearing for the iteration loop**.
Without them, the SFT'd model can't learn to repair its
own proposals from structured synth feedback.

### Total target

20K-50K examples mixing:
- 10% seed,
- 10% paraphrase,
- 60% synthetic (verified),
- 20% failure-feedback (verified + corruption).

---

## Base model selection

| Model | Params | Why | License |
| --- | --- | --- | --- |
| **Qwen2.5-Coder-7B-Instruct** | 7B | Best small code model; well-tuned for structured output; permissive license | Apache 2.0 |
| **DeepSeek-Coder-V2-Lite-Instruct** | 16B (MoE, 2.4B active) | Strong code + cheap inference | DeepSeek (commercial OK) |
| **Codestral-22B** | 22B | Mistral's code-specialist; strong on long-context | Mistral commercial |
| **Qwen2.5-Coder-32B-Instruct** | 32B | Best-quality option; matches GPT-4 on code | Apache 2.0 |
| **Llama-3.1-8B-Instruct** | 8B | Strong general but weaker on code formatting | Llama community |

**Recommendation**: start with **Qwen2.5-Coder-7B-Instruct**.
- Highest-quality permissive small model for code-shape
  outputs.
- Fits in a single 24GB GPU for QLoRA.
- Strongest structured-output behavior pre-training.
- Apache 2.0 license — no commercial restrictions if we
  ever ship the FT'd weights.

Escalate to 32B only if 7B can't capture the
failure-feedback iteration pattern.  Bake-off across 3-4
base models adds ~$50-100 to the cost estimate; do this
before committing to a full FT run.

---

## Fine-tuning framework

| Framework | Strengths | Weaknesses |
| --- | --- | --- |
| **Unsloth** | 2-5× faster than baseline; lowest VRAM; works on single GPU; native QLoRA | Not multi-GPU friendly; less battle-tested for larger models |
| **Axolotl** | Most popular; great docs; multi-GPU ready; YAML config | Slower than Unsloth; more setup |
| **LLaMA-Factory** | All-in-one UI + CLI; supports many models | Less integrated with HF ecosystem |
| **HuggingFace TRL + PEFT** | Canonical, most flexible | Slowest; most setup |

**Recommendation**: **Unsloth for the prototype**, switch
to **Axolotl** if scaling beyond 7B QLoRA.  Unsloth's H100
throughput on 7B QLoRA is ~3K tokens/sec — enough to FT on
30K examples × 1K tokens in ~3 hours.

---

## Where to fine-tune

| Option | $/h (H100 80GB) | Notes |
| --- | --- | --- |
| **RunPod (Community Cloud)** | $1.10-1.50 | Cheapest; some availability variance |
| **Lambda Labs** | $1.99 | Reliable; good docs |
| **Vast.ai** | $1.20-1.80 | Marketplace; variable quality |
| **Modal Labs** | $2.10 (serverless) | Pay-per-second; great for iteration |
| **Together AI fine-tuning API** | ~$0.30 per M tokens | Hands-off; locks you into their endpoint |
| **OpenAI fine-tuning** | ~$25 per M tokens | Only GPT-4o-mini base; closed weights |
| **Local M3 Max** | $0 marginal | MLX framework; works for 7B QLoRA inference, slow for FT |

**Recommendation**:
- **Modal Labs for prototyping** — pay-per-second is great
  for iteration when you're tweaking the dataset.
- **RunPod for production runs** — cheapest H100 hour rate.
- **Avoid Together / OpenAI fine-tune APIs** for the
  prototype — you want full control over dataset format
  and loss-curve introspection.  Re-evaluate once the
  pipeline is stable.

---

## Cost estimate

Assumes Qwen2.5-Coder-7B + QLoRA on 30K examples averaging
1K tokens each:

| Phase | Compute | Wall | $/h | Cost |
| --- | --- | --- | --- | --- |
| Teacher-LLM data gen (50K paraphrase + synthetic) | API | — | — | **~$500** (Haiku) — **$1500** (Sonnet) |
| Synth verification of generated data | 8-core local | 1.5 days | $0 | **$0** |
| Hand-authored seed expansion (curator time) | — | 40-80h | — | **non-monetary** |
| QLoRA FT epoch 1 | 1× H100 | 3-6h | $1.50 | **$5-10** |
| QLoRA FT 3 epochs (typical) | 1× H100 | 9-18h | $1.50 | **$15-30** |
| Eval + ablation runs | 1× H100 | 4-8h | $1.50 | **$6-12** |
| Iteration (3-5 rounds of dataset fixes + retrain) | 1× H100 | 30-90h cumulative | $1.50 | **$50-150** |
| **TOTAL first prototype** | | | | **~$600-1700** |

Escalations:
- **Qwen2.5-Coder-32B**: ~4× FT compute → **+$200-600**.
- **Full FT (no LoRA)**: 5-10× compute → **+$1K-3K**.
  Probably unnecessary — LoRA captures the output-format-
  and-style task well.
- **Base-model bake-off** (3-4 models, 1 epoch each): **+$50-100**.

Realistic budget envelope: **$600-2500** including
escalations.

---

## Risk factors

**R1 — Synth verification loop is the bottleneck.**
Generating 50K candidate `(English, Problem)` pairs
requires running synth on each.  Synth wall-clock variance
is high (1s to 1500s).  Need a hard timeout (~60s) and
discard slow ones.  Could lose 20-40% of synthetic
candidates to timeouts.

**R2 — Distribution mismatch with real user English.**
Verified-benchmark `description` fields are written by
curators familiar with the IR.  Real user docstrings have
different vocabulary, ambiguity, missing information.
**Mitigation**: HumanEval+ docstrings are a free
out-of-distribution test set — the FT'd model should be
evaluated on them even if not trained on them.

**R3 — Skill files are large.**  `problem.skill` +
`debug.skill` combined are ~50K tokens.  On a 32K-context
base model, this is impossible without splitting.  Need
either:
- (a) a 128K-context model (Qwen2.5 supports 128K, slightly
  more expensive at inference), or
- (b) skill-file distillation (compressed reference card
  during FT data prep), or
- (c) RAG over the skill files.

**Recommendation**: distill `problem.skill` + `debug.skill`
into a ~8K-token combined reference card before FT.  The
distilled card lives in the FT'd model's training data
implicitly; the original skills stay authoritative for
curator-driven development.

**R4 — Failure-feedback teaching is hard.**  The iteration
loop assumes the LLM can read structured `NoSolution.hints`
and adjust.  Pure SFT may not teach this — might need DPO
or RLHF on `(failed, repaired)` pairs.  Adds complexity but
is well-trodden.

**R5 — Model selection is empirical.**  The Qwen2.5-Coder-7B
recommendation is based on benchmarks for other tasks.
Could need a bake-off pass.  Budget the +$50-100.

---

## Suggested phase plan

**Phase NL.0 — Skill distillation (1 week)**.  Hand-distill
`problem.skill` + `debug.skill` into an 8K-token reference
card.  Validate by giving the card to GPT-4 / Claude with a
sample HumanEval problem and confirming the model can author
a plausible Problem record from it.  This is also a useful
artifact independent of FT.

**Phase NL.1 — Data generation pipeline (1-2 weeks)**.  Build
the augmentation + synthetic + failure-feedback pipelines.
Run end-to-end on a 1K-example slice; manually inspect.
Settle on the synth-verification timeout, the discard rules,
and the prompt templates.

**Phase NL.2 — Base-model bake-off (3-5 days)**.  1-epoch FT
on 3-4 candidate models with a 5K-example slice.  Evaluate on
a held-out 100-example set of (verified-spec, expected-shape)
pairs.  Pick winner.

**Phase NL.3 — Full FT run (1 week)**.  3-epoch QLoRA on
30K-50K examples.  Run eval on HumanEval GREEN problems.

**Phase NL.4 — Iteration loop integration (1-2 weeks)**.
Wire the FT'd model into `synth.cli` as an English-driver.
Implement the retry-with-failure-feedback loop.  Measure:
convergence rate, average iterations, wall-clock per spec.

**Phase NL.5 — Public demo (1 week)**.  Web UI or CLI:
`synth-from-english "given a list of integers, return the
maximum"` → produces (code, proof).  Ship.

Total realistic timeline (part-time): **6-8 weeks** including
infrastructure debugging.

---

## Open questions (for when we embark)

1. **DPO vs SFT for failure-feedback teaching.**  Worth a
   small ablation in Phase NL.2 or NL.3.
2. **Single-turn vs multi-turn data format.**  Multi-turn
   captures the iteration loop directly; single-turn is
   easier to train on.  Probably multi-turn with a
   max-turns budget of 3-5.
3. **Whether to also fine-tune for Lean proof sketches.**
   §B / Phase Y.2 in RESEARCH.md is the per-instance proof
   sketch task.  Could be the same FT or a separate one.
   Defer until NL front-end ships.
4. **Eval methodology.**  Solve-rate on HumanEval GREEN
   set + convergence-iterations distribution + wall-clock
   percentiles.  Standardize before NL.3.

---

## When to revisit

This doc is parked.  Revisit when:
- A clear demo motivation emerges (talk, paper, blog post
  publication need).
- HumanEval+ coverage push (§N of RESEARCH.md) makes the
  curator workflow expensive enough that automation is
  attractive.
- The synthesis substrate stabilizes enough that the
  underlying capability surface won't shift mid-FT.

Until then: the project's synthesizer is "done enough" for
the curator workflow; FT'd English driver is a delivery
push, not a capability push.
