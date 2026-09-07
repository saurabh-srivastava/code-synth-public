# verina_basic_80 — only_once

VERINA-basic task ported to this repo's proof-theoretic synthesizer and **faithfully verified** (Z3 + Lean, 7 `.solved.lean` proof(s)).

| File | What |
| --- | --- |
| `nl.txt` | VERINA natural-language statement |
| `verina-spec.md` | VERINA signature + precond / code / postcond |
| `problem.py` | our Problem spec (runnable) |
| `synthesized.py` | the synthesized program |
| `invariants.md` | discovered inductive invariant + ranking |
| `fidelity-verdict.md` | spec soundness/completeness vs VERINA's tests |
| `lean/…/*.solved.lean` | the machine-checked Lean proofs |

Reproduce: `python benchmarks/verina/verina_basic_80/problem.py`
