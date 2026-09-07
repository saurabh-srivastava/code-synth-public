# VERINA campaign — status

Honest running report for the `search-based-verina-proving`
campaign.  See [`README.md`](./README.md) for method and
[`../related-work/verina.md`](../related-work/verina.md) for
the framing.

**Scope:** structural triage of all 108 VERINA-basic tasks +
a 4-task pilot + a **68-task fan-out over the expressible
set** + a spec-fidelity pass (`specgen_check.py`) +
output-shape drift triage (`drift_triage.py`).

---

## 0. Headline (fan-out complete)

Of the **72 VERINA-basic tasks our IR can express by type**,
one agent per task attempted a port + synthesis + verification.
After a spec-fidelity pass (to reject silent mis-ports — see
§7), the honest breakdown:

| Outcome | Count | Tasks / meaning |
| --- | --- | --- |
| **Faithfully verified** | **66** | verified `(code, proof)` whose post faithfully captures VERINA's spec (40 mechanically SpecGen-confirmed on VERINA's concrete tests + 26 eyeball-confirmed faithful where SpecGen gapped only on tooling — 2-var `ForAll`, remaining UF interps, out-of-range default) |
| **Partial-fidelity** | **2** | `BubbleSort` (52), `SelectionSort` (87): verified, but against a post *weaker* than VERINA — sortedness (`∀p≤q. A[p]≤A[q]`) **without** the permutation clause.  "Return all zeros" would satisfy our post. |
| **Synth-wedge failure** | **2** | `dissimilarElements` (22), `MoveZeroesToEnd` (35): ported but synthesis did not verify within budget (one 120s Z3 wedge, one Lean-dispatch wedge on `sc2`) |
| **Mis-port** | **1** | `FindEvenNumbers` (60): agent silently solved *count the evens* instead of *return them*; caught by `drift_triage.py` (output shape scalar ≠ VERINA's array) |
| **Not-expressible** | **1** | `FindEvenNumbers` (34): rigorous NOT-EXPRESSIBLE (see `reach-limits/`) |

So: **66 of 72 expressible = 66 of all 108 VERINA-basic
(61%) carry a faithful machine-checked proof**, next to
VERINA's best-model **22.2%** refined ProofGen on the same
tier.

**The mandatory caveats hold** (and matter): we *synthesize
code to be provable* (vs prove given code); scaffolding is
heavy (of the verified, 42 straight clones / 17 adapted / 5
authored); and the 36 `encodable-not-yet` + Float tasks
weren't attempted.  So it is strong evidence for
proof-as-search, not a clean like-for-like win.

### The two genuinely interesting findings (worth more than the number)

1. **A single concrete reach limit explains ALL 6 non-faithful
   outcomes: multiset / permutation / order-preservation.**
   `FindEvenNumbers` (filter, → mis-port + not-expressible),
   `MoveZeroesToEnd` (stable partition, → wedge),
   `dissimilarElements` (set difference + nodup, → wedge), and
   `BubbleSort`/`SelectionSort` (sort, → partial-fidelity) all
   require "the output is a permutation / sub-multiset of the
   input."  The integer-array IR (total Z3 maps + separate
   length; no `toList`/`count`/`idxOf`/`push`) cannot state
   that without a UF inside a `Select` index inside a `∀`,
   hitting the E-matching cliff — so the synthesizer either
   wedges, or verifies against a post that quietly drops the
   permutation clause.  This is the one clean, recurring thing
   proof-theoretic synthesis over predicate abstraction can't
   currently do here.  (Sidestep sketched in `reach-limits/`.)

2. **Fidelity checking is load-bearing, not decoration.**
   `FindEvenNumbers` (60) is proof that an autonomous agent,
   when stuck, will silently reformulate an inexpressible task
   into an expressible-but-different one that still *verifies*.
   Without `specgen_check.py` + `drift_triage.py` we'd have
   counted it as a win.  Self-reported verification is not
   fidelity.

---

## 1. Structural triage (unbiased, all 108 VERINA-basic)

`python verina/triage.py`:

| Reach | Count | Meaning |
| --- | --- | --- |
| **expressible today** | **72** | synthesizable in the current IR without new encodings |
| **encodable-not-yet** | **34** | engineering gaps, NOT limits — see below |
| **fundamental** | **2** | Float only (non-integer numerics) |

The 34 "encodable-not-yet" are blocked only by types we
haven't wired into the IR yet, all of which reduce to the
integer-array + multi-output + UF substrate:

| Blocker | Tasks | Encoding path |
| --- | --- | --- |
| tuple / `×` | 11 | multiple outputs (already supported) |
| String | 10 | int/codepoint sequence |
| List | 7 | our Array |
| Char | 5 | int codepoint |
| Option | 2 | tag+value / sentinel |
| Map | 1 | UF- or array-backed |
| UInt / `Int->Bool` | (in above) | bounded int / Z3 BV; UF with axioms |

Only **2 tasks (Float)** touch a plausibly-fundamental
limit — and even that is hedged, since Z3 and Lean both
have real arithmetic.  So the honest reach statement is:
**72 expressible now; ~34 more behind unwritten encodings;
2 near a real edge.**

---

## 2. Pilot (4 tasks) — all verified, all spec-faithful

Chosen to span {scalar, array→scalar, array→array} ×
{pure-Z3, axiom-heavy Lean}.  **These were deliberately
picked to map onto shapes we already support** — a
proof-of-pipeline, not a random sample (§5).

| # | VERINA task | Shape | Verified | Wall | Verifier | Trust surface | SpecGen fidelity |
| --- | --- | --- | --- | --- | --- | --- | --- |
| q1 | `verina_basic_1` hasOppositeSign | scalar | ✅ (4 sols) | 0.09s | pure Z3 | **none** | 4/4 pre+post, sound+complete |
| q2 | `verina_basic_47` arraySum | array→scalar | ✅ | 153.8s | Z3 + Lean | `sum` base + recurrence axioms | 4/4 |
| q3 | `verina_basic_57` CountLessThan | array→scalar | ✅ | ~190s* | Z3 + Lean | 3 `count_less` axioms | 5/5 |
| q4 | `verina_basic_32` swapFirstAndLast | array→array | ✅ | 0.07s | pure Z3 | **none** | 4/4 |

\* q3 representative run ~190s; a contended run measured
819s (multi-agent CPU contention, not algorithmic).

**4/4 synthesized a verified `(code, invariant, ranking,
proof)`.  4/4 pass VERINA's own test-based spec
soundness+completeness check** (`python
verina/specgen_check.py --all`) — our ported specs
reproduce VERINA's ground-truth outputs on every concrete
test, so the port did not silently change the problem.

Synthesized invariants (from the runs):
- q2: `result == sum(A, i) ∧ 0 ≤ i ≤ n`, ranking `n - i`.
- q3: `c == count_less(A, threshold, i) ∧ 0 ≤ i ≤ n`, ranking `n - i`.
- q1/q4: straight-line, no loop invariant.

---

## 3. The three honest numbers (per plan §7.2)

**(a) How many we can synthesize + verify at all.**
Pilot: 4/4.  Full expressible set (72): not yet run — this
is the fan-out still owed.  The pilot shows the pipeline
round-trips VERINA→Problem→(code,proof) cleanly for the
shapes it covers.

**(b) Scaffolding cost — hand-authored vs. cloned template.**
All 4 pilot tasks reused an existing benchmark's template +
predicate space almost verbatim:
- q1 ← `sign`/`abs` (SB(n=2) scalar)
- q2 ← `sum_array` (sum UF + recurrence)
- q3 ← `count_equal`/`array_neg_count` (case-split count UF)
- q4 ← `swap_first_last` (nested Update, ghost pre-state)

So per-task scaffolding was **low — but only because the
pilot was chosen to be clonable.**  The axiom-heavy pair
(q2, q3) still required authoring/adapting `.solved.lean`
companions (3 and 7 respectively) — real work, but
mechanical adaptation of an existing proof, not new proof
discovery.  The unbiased scaffolding question is answered
only by the tasks that DON'T map to an existing shape.

**(c) Wall-clock + trust surface.**  Pure-Z3 tasks: sub-second,
zero trusted axioms (fully machine-checked).  Axiom-heavy
tasks: 2.5–3 min, trust surface = the handful of UF
recurrence axioms that DEFINE the fold (sum / count).  Those
axioms are the entire "trust me"; every loop-preservation
step is Lean-proved.  The SpecGen check independently
confirms those axioms reproduce VERINA's outputs.

---

## 4. Comparison to VERINA (careful)

VERINA's best model reaches **22.2% ProofGen** on
VERINA-basic with 64× refinement (3.6% pass@1).  Our pilot
is **4/4** — but this is **not** a like-for-like number and
must not be reported as one:

- We **synthesize code to be provable**; VERINA proves a
  **given** reference implementation.  We never face an
  adversarial implementation.
- The pilot was **chosen to be clonable**.  The honest
  denominator is the 72 expressible tasks, most of which
  won't map onto an existing benchmark as cleanly.
- We add **per-task scaffolding** (template + predicate
  space); VERINA's setup is end-to-end autonomous.

What the pilot *does* establish: on tasks our IR can
express, the **proof-as-search** architecture produces a
Lean-checked proof where **proof-as-generation** (VERINA's
LLM-writes-Lean-tactics) mostly fails — and the ported
specs are demonstrably faithful to VERINA's.  That is
evidence for the architectural bet, not a headline win.

The number that would mean something (still owed):
**"of VERINA-basic's 72 expressible tasks, our synthesizer
produced a verified (code, proof) for N, with the template
hand-authored for M"** — reported next to VERINA's 22.2%.

---

## 5. What the full run needs

1. **Fan out over the remaining ~68 expressible tasks**
   (72 minus the 4 piloted), one Problem port each, via the
   community-validation agent pattern.  Group by shape so
   template reuse is maximized and the genuinely-novel ones
   are visible.
2. **Record per task**: verified? wall-clock? template
   cloned-vs-authored? trust surface? SpecGen fidelity?
3. **Extend `_UF_INTERP` / `_PORT_MAP`** in
   `specgen_check.py` for each new port (the fidelity claim
   is mandatory, not optional).
4. **Log the tasks that resist** — an expressible-by-type
   task that still won't synthesize (predicate space too
   large, control flow we don't template, spec needs a
   quantifier alternation we can't discharge) is itself a
   finding about the reach of proof-theoretic synthesis.
5. **Optionally, start encoding the 34**: tuple→multi-output
   is nearly free and unlocks 11 tasks; String/List/Char are
   the next tier.  Each encoding written moves tasks from
   "encodable-not-yet" to "expressible."

---

## 6. Reproduce

```bash
git clone --depth 1 https://github.com/sunblaze-ucb/verina.git \
    /private/tmp/verina-data
.venv/bin/python verina/triage.py                 # triage 108
.venv/bin/python benchmarks/verina/verina_basic_47_array_sum.py
.venv/bin/python verina/specgen_check.py --all    # fidelity
```

Pilot artifacts: `benchmarks/verina/verina_basic_{1,32,47,57}_*.py`
+ `lean/SynthLean/Y2Corpus/verina_basic_{47,57}_*/`.
