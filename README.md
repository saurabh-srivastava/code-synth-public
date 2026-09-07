# Synthesizer

[![CI](https://github.com/saurabh-srivastava/code-synth/actions/workflows/ci.yml/badge.svg)](https://github.com/saurabh-srivastava/code-synth/actions/workflows/ci.yml)

A proof-theoretic program synthesizer.  Given a
**control-flow template** (loops / conditionals / recursion
shapes) and a **predicate space** (candidate atoms for
invariants, guards, transitions, and ranking functions), it
produces:

- **Code** — a filled-in program that satisfies the spec.
- **Proof** — invariants, ranking functions, and
  coverage / preservation obligations verified by Z3 and / or
  Lean 4 (both backends supported; Lean handles obligations
  where SMT is unreliable).

A clean-room reimplementation of *Pragna* (POPL'10 + PLDI'11),
extended with a dual SMT + interactive-theorem-prover
verification pipeline.  The LLM front-end is deliberately
decoupled: the synthesizer is the **trustworthy verifier**;
the LLM (any size, any source) is the **untrusted proposer**.

## North stars

Three long-horizon dimensions:

1. **From correctness to full resource semantics.**  Today
   the synthesizer proves *partial correctness +
   termination*.  The target is `(code, proof)` carrying
   worst-case runtime and space bounds as well — PLDI'09-
   style resource templates layered onto the same IR.
   [`COST_INVS.md`](./COST_INVS.md) is the design doc;
   substrate has landed (2026-05-22).

2. **From single function to full programs.**  Today the
   unit of synthesis is one function.  The end goal is
   multi-function modules with explicit interfaces +
   assume-guarantee composition.  See
   [`PRINCIPLES.md`](./PRINCIPLES.md) §NS-2.

3. **Algorithmic discovery + bounds verification.**
   Templates cover a *space* of programs, not a single one.
   POPL'10's Strassen template surfaced 7-multiplication
   2×2 matrix multiplications absent from the published
   literature; recent exploration produced Z3-kernel-checked
   structural results on the open-frontier Hopcroft-Kerr
   R(2,3,2) ≤ 11 sub-tensors and the literal-coefficient
   ±1 K=7 lower bound for 2×2 matmul at Σ|nz| ≥ 35.  The
   goal: certify — and where possible discover — programs
   that are provably correct, provably terminating, and
   provably resource-optimal.  See
   [`OPEN_PRBS.md`](./OPEN_PRBS.md) for the catalog.

## Quick start

For from-scratch install instructions (Python venv, Lean
toolchain, mathlib), see [`SETUP.md`](./SETUP.md).

```python
from synth import Problem, SB, Loop, Var, solve

PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 1",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= m))",
    atoms    = {
        "s@B0":   [{"m": "A[0]", "i": "1"}],
        "tau@L0": ["ForAll(lambda k: Implies(0 <= k and k < i, A[k] <= m))",
                   "i <= n"],
        "g@L0":   ["i < n"],
        "phi@L0": ["n - i"],
        "g@B1.0": ["A[i] > m"], "s@B1.0": [{"m": "A[i]", "i": "i + 1"}],
        "g@B1.1": ["A[i] <= m"], "s@B1.1": [{"i": "i + 1"}],
    },
)

result = solve(PROBLEM)
print(result.best.code)            # pseudocode + proof annotations

from synth import emit_c, emit_py, emit_rust
print(emit_c   (result.best, PROBLEM, fname="max_array"))
print(emit_py  (result.best, PROBLEM, fname="max_array"))
print(emit_rust(result.best, PROBLEM, fname="max_array"))
```

`solve()` returns a verified solution, an UNSAT diagnosis
(predicate space too narrow), or a Timeout with hole-size
telemetry.  No hallucinated proofs.

## Status (2026-06-07)

**~80 verified benchmarks across 8 tiers.**  Headline
recent work on the L1.6 max-matching family: Slice 2.C
(max matching with concrete `IsMatching` predicate and a
Tier-1 PROVEN `flip_preserves_im` theorem, 131.9s, 2
trusted axioms) and Gale-Shapley closure (mod-cycled GS,
86.1s, 6 Tier-1 PROVEN helpers, 17 step axioms, *zero*
algorithm-step preservation axioms).  Both validate the
recursive-UF step-axiom encoding pattern.

The synthesizer is **sound by default** (Z3 UNKNOWN on
soundness-critical kinds is treated as rejection; Lean
fallthrough recovers what's actually provable).  See
[`SOUNDNESS.md`](./SOUNDNESS.md) for the policy and
[`BENCHMARKS.STATUS.md`](./BENCHMARKS.STATUS.md) for the
per-benchmark catalog (path / verifier / V/S / wall-clock /
helper tier / discoveries / caveats).

Phase-by-phase history lives in
[`CHANGELOG.md`](./CHANGELOG.md).

## Where to read next

| Doc | Audience | Purpose |
| --- | --- | --- |
| [`BENCHMARKS.STATUS.md`](./BENCHMARKS.STATUS.md) | public + impl | Per-benchmark catalog (canonical "what's verified") |
| [`SOUNDNESS.md`](./SOUNDNESS.md) | public + impl | Soundness posture: what "verified" means + safety nets |
| [`PRINCIPLES.md`](./PRINCIPLES.md) | impl | Governing principles + always-on reminders + north-star expansions |
| [`CHANGELOG.md`](./CHANGELOG.md) | impl + future | Phase-by-phase history (everything but the most recent ~3 phases) |
| [`CLAUDE.md`](./CLAUDE.md) | impl | Session TL;DR: repo layout + most-recent phases + decisions |
| [`CONTRIBUTING.md`](./CONTRIBUTING.md) | contributors | Phase-completion routine + experience-report rule + style |
| [`DESIGN.md`](./DESIGN.md) | impl | Long-form design doc (algorithm, encoding, hurdles).  Original name: `plan.md`. |
| [`SETUP.md`](./SETUP.md) | new users | From-scratch install: Python venv, Lean toolchain, sanity-check |
| [`RESEARCH.md`](./RESEARCH.md) | impl + future | Post-foundations research threads (NL front-end, Lean backend, completed deep-dives at §K.B/§K.D moved to `RESEARCH.COMPLETED.md`) |
| [`RESEARCH.LEAN.md`](./RESEARCH.LEAN.md) | impl | Lean backend specifics + Ring 1 end-of-MVP review |
| [`OPEN_PRBS.md`](./OPEN_PRBS.md) | impl + future | Catalog of open problems (Karatsuba GF(2^k), sub-cubic min-plus matmul, etc.) |
| [`COST_INVS.md`](./COST_INVS.md) | impl + future | Design plan for cost-bound invariants (north star #1 substrate) |
| [`HUMANEVAL.STATUS.md`](./HUMANEVAL.STATUS.md) | impl + future | Triage of 164 HumanEval+ problems on 5-level rubric |
| [`NL_FRONTEND.md`](./NL_FRONTEND.md) | impl + future | Parked plan: fine-tuned LLM English → `Problem` driver |
| [`EXPERIENCE_REPORT.md`](./EXPERIENCE_REPORT.md) | public (long form) | Case studies: "Is Claude a good research assistant?" |
| [`problem.skill`](./problem.skill) | LLM driver | Happy-path guide for authoring a `Problem` |
| [`debug.skill`](./debug.skill) | LLM driver | What to do when something goes wrong |
| [`ref/PAPERS.md`](./ref/PAPERS.md) | impl | POPL'10 / PLDI'11 / PLDI'09 paper summaries |
| [`COMMUNITY_VALIDATION_REPORT.md`](./COMMUNITY_VALIDATION_REPORT.md) | public | 8 rounds of fresh-Claude audit: round narratives, lineups, friction findings |
| [`COMMUNITY_VALIDATION_BACKLOG.md`](./COMMUNITY_VALIDATION_BACKLOG.md) | impl | 14 banked friction findings (verified premises, not yet shipped) |

## Community-validation branch

A long-running audit (v1–v9) tested whether fresh Claude
agents with no prior context can author + synthesize
verified benchmarks using only the docs in this repo.
The audit shipped F1–F20 + F28 to main and produced 25
agent-authored benchmarks across 9 rounds — 3 of them
(`is_palindrome`, `fibonacci_array`,
`matrix_diagonal_sum`) merged into main as exemplars of
algorithmic patterns that weren't previously represented.

The full per-round history (every agent's commit, every
merge, every report) lives on a single umbrella branch:

```
git fetch && git checkout community-validation
```

This branch is the canonical record of the audit: it
merges `community-validation-v1` through
`community-validation-v9` and carries the full
[`COMMUNITY_VALIDATION_REPORT.md`](./COMMUNITY_VALIDATION_REPORT.md)
narrative.

**For new contributors authoring benchmarks**: base your
working tree off the `community-validation` umbrella
branch, not `main`.  The umbrella has all 25
agent-authored benchmarks visible as reference patterns
(plus the 3 also on main).  Only the 3 main-promoted
ones are required-quality; the rest are audit artifacts
with variable polish but useful for "find me a benchmark
that does X" lookups.  v9 surfaced this gap when agents
working off `main` couldn't find references named in
their task prompts.

## License

GPL-3.0-or-later.  See [`LICENSE`](./LICENSE) for full text
and [`CITATION.cff`](./CITATION.cff) for citation metadata.
