# verina_basic_10 — isGreater

VERINA-basic task ported to this repo's proof-theoretic synthesizer and **faithfully verified** (Z3 only, 0 `.solved.lean` proof(s)).

| File | What |
| --- | --- |
| `nl.txt` | VERINA natural-language statement |
| `verina-spec.md` | VERINA signature + precond / code / postcond |
| `problem.py` | our Problem spec (runnable) |
| `synthesized.py` | the synthesized program |
| `invariants.md` | discovered inductive invariant + ranking |
| `fidelity-verdict.md` | spec soundness/completeness vs VERINA's tests |

Reproduce: `python benchmarks/verina/verina_basic_10/problem.py`
