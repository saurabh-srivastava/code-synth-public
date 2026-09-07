# Campaign: search-based VERINA proving

Running this repo's proof-theoretic synthesizer against the
VERINA-basic benchmark (arXiv:2505.23135,
`sunblaze-ucb/verina`), per the plan in
[`../related-work/verina.md`](../related-work/verina.md) §7.

**The thesis under test:** VERINA measures LLM-authored Lean
proofs and finds a wall (best model ~3.6% ProofGen pass@1,
~22% with 64× refinement on the basic tier).  Our approach
*searches* for proof-carrying programs instead of generating
proofs.  Does that actually clear more of VERINA-basic, and
at what scaffolding cost?

**This is not a claimed win.**  It's an honest experiment.
We report: how many tasks we can express at all, how many we
verify, how much per-task scaffolding it took, and the trust
surface each result rests on.

## Layout

| File | What |
| --- | --- |
| `triage.py` | Classifies all 108 VERINA-basic tasks by whether our IR can express them (expressible / encodable-not-yet / fundamental). Writes `triage.json` (gitignored — embeds VERINA text, regenerable). |
| `drift_triage.py` | Cheap output-SHAPE check of each port vs VERINA's return type — catches gross mis-ports for free. |
| `specgen_check.py` | VERINA's test-based spec soundness/completeness check on our ported specs (auto-derives the var mapping; UF interpretations = the explicit fidelity claim). |
| `materialize_e2e.py` | Generates the per-task end-to-end bundle (NL → Problem → synthesized code+invariant → Lean proofs). |
| `restructure.py` | One-shot: converts the flat fan-out layout into per-task dirs (full bundle for faithful, single category `.md` for the rest). |
| `STATUS.md` | The honest report: triage numbers, fan-out taxonomy, the reach-limit finding. |
| `reach-limits/` | Rigorous NOT-EXPRESSIBLE analyses (e.g. the `findEvenNumbers` filter). |

### Per-task directories

Each attempted task lives in `../benchmarks/verina/<vid>/`:

- **Faithfully verified** — the full self-contained bundle:
  `README.md`, `nl.txt`, `verina-spec.md`, `problem.py`
  (runnable), `synthesized.py`, `invariants.md`,
  `fidelity-verdict.md`, and `lean/SynthLean/Y2Corpus/<vid>/*.solved.lean`
  (the machine-checked proofs).
- **Non-faithful** (partial-fidelity / synth-wedge / mis-port /
  not-expressible) — a single `<category>.md` with the
  serialized data + a detailed outcome note.  No misleading
  half-bundle.

The relocated proofs are still mechanically re-checked in CI
(`tests/test_y2corpus.py` scans both `lean/SynthLean/Y2Corpus/`
and `benchmarks/verina/*/lean/`).

## Reproduce

```bash
# 1. Clone the VERINA data (once).
git clone --depth 1 https://github.com/sunblaze-ucb/verina.git \
    /private/tmp/verina-data

# 2. Structural triage of all 108 basic tasks.
.venv/bin/python verina/triage.py            # -> triage.json + summary

# 3. Synthesize any faithfully-verified task from its dir.
.venv/bin/python benchmarks/verina/verina_basic_<n>/problem.py

# 4. Spec-fidelity + drift checks.
.venv/bin/python verina/specgen_check.py --all
.venv/bin/python verina/drift_triage.py
```

## Honest accounting rules

1. **Expressible ≠ verified.** The triage's "expressible"
   count is a structural upper bound (types our IR can hold),
   not a synthesis claim.
2. **Report scaffolding.** Every ported task records whether
   its control-flow template + predicate space were
   hand-authored or LLM-guessed. That is the cost side of the
   ledger vs. VERINA's end-to-end-LLM autonomy.
3. **Report the trust surface.** Each verified task lists the
   UF axioms it rests on. "Provably correct" always means
   "w.r.t. this spec + these axioms."
4. **Spec fidelity is separate from proof success.** A task
   can synthesize + verify against *our* spec while our spec
   fails to match VERINA's intent. `specgen_check.py` catches
   that; both numbers get reported.
5. **No cherry-picking without saying so.** The pilot set was
   chosen to map onto shapes we already support (a
   proof-of-pipeline). The triage is the unbiased number.
