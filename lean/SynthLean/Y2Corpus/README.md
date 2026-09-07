# Y2Corpus — Phase Y.2 training data for the driver-LLM

Per `RESEARCH.md` §D, Phase Y.2's driver-LLM constructs per-instance
Lean proof sketches for obligations the synthesizer's generic Lean
tactic chain can't auto-close.  This directory is the **training
corpus** for that work: each obligation that Lean's generic chain
couldn't dispatch is paired with a **mechanically-checked** Lean
companion encoding either how to discharge it (`.solved.lean`) or
why it's unprovable (`.invalid.lean`).

## File layout

The corpus is organized as **per-benchmark subdirectories**, each
containing one or more (failed, companion) **pairs**:

```
Y2Corpus/
├── <benchmark>/
│   ├── <stem>.failed.lean      # auto-dumped — Lean couldn't close
│   ├── <stem>.solved.lean      # OR — hand-written proof closes it
│   └── <stem>.invalid.lean     # OR — Lean-checked counterexample
```

Each `<stem>` is `<theorem_name>_class_<N>` — e.g.,
`sc1_fallthrough_class_3` — uniquely identifying one (safety
constraint, attribute-class subset) tuple from the PLDI'09 reduction.

### File types

- **`<stem>.failed.lean`** — committed.  Auto-dumped by
  `synth.lean_backend.verify` when the generic Lean tactic chain
  fails, errors, or times out on that obligation.  The first line
  is a `-- ...` comment recording the failure mode.  The rest is
  the verbatim Lean source the generic chain attempted.  These are
  the **inputs** of training pairs for the driver-LLM.

- **`<stem>.solved.lean`** — committed (when applicable).  A
  hand-written or driver-LLM-generated Lean theorem that proves
  the same obligation as the `.failed.lean`.  Should:
    - `import SynthLean.Basic`;
    - re-declare the UF / axioms locally (so the file is
      self-contained ICL data);
    - prove the obligation's theorem statement;
    - type-check cleanly under `lake env lean`.

- **`<stem>.invalid.lean`** — committed (when applicable).  A
  Lean theorem of the form
  ```lean
  theorem <stem>_is_invalid :
      ∃ <vars>, <hypotheses> ∧ ¬ <goal> := by ...
  ```
  i.e., a **mechanically-verified existential counterexample**
  showing the obligation is unprovable.  Refute with concrete
  witnesses (numeric where possible; UF applications where the
  axioms constrain only some values).  These are **negative
  training examples**: the driver-LLM should learn to construct
  such counterexamples rather than attempting doomed proofs.

Each `<stem>.failed.lean` has exactly one companion — either
`.solved.lean` or `.invalid.lean`, never both.

### Why mechanical checking?

A prose comment claiming "this obligation is invalid because i = 0
falsifies it" is unverifiable — the comment could be wrong, the
witness could fail to satisfy a hypothesis, the conclusion could be
mis-stated.  A Lean proof `∃ ..., hypotheses ∧ ¬ goal` is checked
by Lean's kernel: the corpus cannot lie.

CI runs `tests/test_y2corpus.py`, which invokes `lake env lean` on
every `.invalid.lean` / `.solved.lean`.  Drift between a
`.failed.lean` and its companion — e.g., the translator's encoding
shifts and the companion no longer matches the obligation — is
caught immediately.

## How a (failed, companion) pair is built

1. **Run the benchmark** with `Problem.dump_lean_failures_dir =
   "lean/SynthLean/Y2Corpus/<benchmark>"`.  Auto-dumps every
   class Lean's generic chain couldn't close.
2. **Inspect each dump** to determine: is the τ subset valid but
   the tactic chain too weak (→ `.solved.lean`), or is the subset
   genuinely insufficient (→ `.invalid.lean`)?
3. **For `.solved.lean`**: write a Lean proof of the obligation's
   theorem statement.  Verify with `lake env lean <file>`.
4. **For `.invalid.lean`**: state the negation as a Lean theorem
   `∃ <vars>, <hyps> ∧ ¬ <goal>` and discharge it with concrete
   witnesses.  Verify with `lake env lean <file>`.
5. Commit both `.failed.lean` and its companion together.

## Current entries

- `factorial/` — multiplicative scalar UF recurrence.  5 dumps:
  - sc1 family (classes 0–3): all `.invalid.lean` — every subset
    is missing the τ atom `i ≥ 1`, the precondition for
    `user_axiom_1` (the recurrence).  Counterexamples witness
    at i = 0 (where `result * 0 = 0` but `fact(0) = 1`).
  - sc3 family (class 0): `.invalid.lean` — ranking-LB obligation
    with empty τ; counterexample at n = 0, i = 2.

- `array_product/` — UF-over-array recurrence with multiplication.
  Same shape as factorial but with `prod : (Int → Int) → Int → Int`.
  1 dump:
  - sc1 class 0: `.invalid.lean` — missing `0 ≤ i` τ atom;
    counterexample at i = -1 with `A = (fun _ => 0)`.

## Z3 nondeterminism and corpus stability

Lean fallthrough triggers ONLY on classes Z3 returns UNKNOWN for.
Z3's per-class behavior varies across machines and runs, so the
set of dumped classes is not 100% reproducible.  Operating
discipline:

- Treat the corpus as a growing accumulation of (failed, companion)
  pairs, not a fixed test oracle.
- `expected_lean_hits` on each `Problem` is INFORMATIVE-only; it
  flags drift without failing CI.
- `expected_solutions` is the SOUNDNESS oracle: if the synthesizer
  accepts an unsound assignment due to a missing rejection, the
  solution count diverges and CI fails.
- The corpus mechanical-check gate enforces that every committed
  companion still type-checks — so even when fresh dumps land,
  past curation work isn't silently broken.
