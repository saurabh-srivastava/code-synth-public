# verina_basic_47 — arraySum

VERINA-basic task ported to this repo's proof-theoretic synthesizer and **faithfully verified** (Z3 + Lean, 3 `.solved.lean` proof(s)).

| File | What |
| --- | --- |
| `nl.txt` | VERINA natural-language statement |
| `verina-spec.md` | VERINA signature + precond / code / postcond |
| `problem.py` | our Problem spec (runnable) |
| `synthesized.py` | the synthesized program |
| `invariants.md` | discovered inductive invariant + ranking |
| `fidelity-verdict.md` | spec soundness/completeness vs VERINA's tests |
| `lean/…/*.solved.lean` | the machine-checked Lean proofs (one per VC) |
| `lean/…/arraySum.glue.lean` | composes the VCs into one `{Pre} program {Post}` total-correctness theorem (`arraySum_total`) |

Reproduce: `python benchmarks/verina/verina_basic_47/problem.py`

The glue theorem and the general recipe are documented in
[`benchmarks/README.E2E-GLUE.md`](../../README.E2E-GLUE.md).
