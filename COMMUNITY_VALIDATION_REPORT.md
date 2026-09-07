# Community-validation rounds: v1 → v2 → v3 → v4 → v5 → v6 → v7 → v8 progression

**Author:** main-agent (Claude Opus 4.7) under direction.
**Dates:** 2026-06-07 to 2026-06-09.
**Purpose:** Audit codebase readiness for outside consumption by spawning
fresh subagents (no prior context) on isolated git worktrees and measuring
how often they can author + synthesize a verified benchmark using only the
repo's docs (`README.md`, `SETUP.md`, `problem.skill`, `debug.skill`,
`DESIGN.md`, `PRINCIPLES.md`, `CLAUDE.md`).

The "community" here is a Claude agent that just walked into the
repo. If they can ship one verified benchmark end-to-end without
escalating to me, an outside human contributor can probably do
the same.

---

## Headline

| Round   | Agents | Verified | Stalled | Notes |
| ---     | ---    | ---      | ---     | ---   |
| **v1**  | 5      | **2/5**  | 3/5     | baseline; 3 watchdog timeouts traced to per-class Lean budget vs cold-mathlib load |
| **v2**  | 5      | **5/5**  | 0/5     | post F1–F5 (mathlib warm-up + `validate_synthlean_import` + collision check + skill prefs) |
| **v3**  | 3      | **2/3**  | 1/3     | post F6+F7+F9 (Core migration + wedge bump + cache-first); 1 new failure mode discovered |
| **v4**  | 2 of 3 | **2/2**  | 0/2     | post F10+F11+F12 (worktree-rebuild docs + `hyp_for(role=...)` + Lean-keyword check); Q3 (HARD) abandoned due to model-side wedge unrelated to the project |
| **v5**  | 3      | **3/3**  | 0/3     | MEDIUM+MEDIUM+HARD lineup; both MEDIUMs used `.solved.lean` cache successfully; HARD chain-aware benchmark closed pure-Z3 surprise |
| **v6**  | 3      | **3/3**  | 0/3     | post F13–F20 (8 friction fixes from v5 audit); MEDIUM+MEDIUM+HARD; HARD finally exercised F11 `hyp_for` chain-aware binders (`h_i<k>_<lid>_tau_*`) — first round to truly hit the chain-aware Lean path |
| **v7**  | 3      | **3/3**  | 0/3     | NEW algorithmic types (pair-of-consecutive flag-fold, right-to-left scan, 2D array indexing); both HARDs verified with axiom-heavy Lean dispatch; first agent-authored 2D benchmark beyond `matrix_init` |
| **v8**  | 3      | **3/3**  | 0/3     | post F28 (ranking-cache-miss dump); HARD+HARD+HARD lineup with NEW algorithmic types (two-pointer toward middle, self-referential array recurrence, late-binding witness); first agent-authored two-pointer benchmark; revealed worktree mathlib cold-start cost + dual-dispatch bug |

**Success rate trajectory: 40% → 100% → 67% → 100% (2/2 returned) → 100% → 100% → 100% → 100%.**

The v3 drop is not a regression: agents tackled harder problems
(EASY+MEDIUM+HARD lineup), and the one stall surfaced a NEW
worktree/Lean-build issue distinct from anything v1 or v2 saw.

The v4 round's Q3 (HARD `find_min_max_two_pass`, designed
specifically to exercise F10+F11) was abandoned mid-run
after the agent went silent for 1h 40m with no processes
running and no transcript activity — diagnosed as a
model-side wedge unrelated to the project's infrastructure
(the agent had only just begun reading reference patterns
when it stopped). No lessons banked from Q3; the run is
treated as a non-result, not a data point.

---

## Round v1 — 2026-06-07

**Branch:** `community-validation` (merged: cv-p1..cv-p5)
**Lineup:** `sum_of_squares`, `count_positive`, `prefix_sums`,
`classify_triangle`, `gcd_lcm` (all MEDIUM).

| Agent | Benchmark         | Outcome  | Wall   |
| ---   | ---               | ---      | ---    |
| P1    | sum_of_squares    | ✅ 147s  | within budget |
| P2    | count_positive    | ❌ STALLED  | watchdog timeout |
| P3    | prefix_sums       | ❌ STALLED  | watchdog timeout |
| P4    | classify_triangle | ✅       | within budget |
| P5    | gcd_lcm           | ❌ STALLED  | watchdog timeout |

**Root cause of 3 stalls:** Per-class Lean dispatch budget
(15s) was tight against the cold-mathlib olean load
(~10–15s on a fresh `lake env lean` process), so the first
real dispatch often timed out and the agent's outer
watchdog reaped after 10 min of no progress. Compounded by
parallel disk contention as 5 agents hit Lean at once.

**Findings banked (F1–F5):**
- **F1** — Mathlib warm-up step in `lean/setup.sh` and
  added it to the docs (`SETUP.md` §3).
- **F2** — `HelperRegistry.validate_synthlean_import()`
  method so authors get a clear warning when their
  `Helpers.lean` imports something the codegen path can't
  resolve.
- **F3** — `Problem.__post_init__` collision check on
  `dump_lean_failures_dir`: prevents two benchmarks from
  silently sharing a dump dir.
- **F4** — `problem.skill` REC 11.6 makes the
  `.solved.lean` cache-companion path the recommended
  authoring approach (vs `HelperRegistry`, which is more
  ceremony for the same effect).
- **F5** — Lesson #67 banked in `CLAUDE.md` about the
  cold-mathlib trap.

---

## Round v2 — 2026-06-08 (morning)

**Branch:** `community-validation-v2` (merged: cv-v2-p1..cv-v2-p5)
**Same 5-benchmark lineup re-run.**

| Agent | Benchmark         | Outcome  | Wall   |
| ---   | ---               | ---      | ---    |
| P1    | sum_of_squares    | ✅ 145.3s | reproduced v1 result |
| P2    | count_positive    | ✅       | first-time pass |
| P3    | prefix_sums       | ✅       | first-time pass |
| P4    | classify_triangle | ✅       | reproduced v1 result |
| P5    | gcd_lcm           | ✅       | first-time pass |

**5/5 returned with verified solutions.** No watchdog
timeouts. Mathlib warm-up + better docs were sufficient to
close the v1 stalls.

**Findings banked (F6+F7+F9):**
- **F6** — Bulk-migrated `.solved.lean` companions from
  `import SynthLean.Basic` (with mathlib, ~5s typecheck) to
  `import SynthLean.Core` (mathlib-free, ~2s typecheck)
  where the proofs don't actually need mathlib. Result:
  **128 of 223 companion files** moved to Core; 95 stayed
  on Basic (factorial, fib, gcd, kadane, etc.). All 241
  Y2Corpus tests still pass.
- **F7** — Bumped `Problem.wedge_threshold` default from 30
  → **200**. With cache-as-primary, partial-subset
  enumeration can need ~hundreds of dispatches per
  constraint before hitting the full-τ cube that matches
  the cache.
- **F9** — Cache-first reorder in
  `synth/lean_backend/verify.py`: consult `.solved.lean`
  companions BEFORE running the generic tactic chain.
  Without this, every per-class dispatch ran the chain
  (5–15s, often timing out) and only THEN checked the
  cache, wasting all that work.

(F8 — making `HelperRegistry.validate_synthlean_import` a
hard error instead of a warning — was rejected: the lake
build resolves via olean cache so the warning is genuinely
soft.)

---

## Round v3 — 2026-06-08 (evening)

**Branch:** `community-validation-v3` (merged: cv-v3-q1..cv-v3-q3)
**Lineup:** EASY + MEDIUM + HARD (3 agents, 60-min budget each).

| Agent | Benchmark            | Difficulty | Outcome   | Wall   |
| ---   | ---                  | ---        | ---       | ---    |
| Q1    | `is_strictly_sorted` | EASY       | ✅ 0.30s  | pure Z3; copied `is_sorted` pattern |
| Q2    | `histogram_3buckets` | MEDIUM     | ✅ 68.3s  | 3-attempt iteration; validated F6+F7+F9 |
| Q3    | `count_pairs_equal`  | HARD       | ❌ STALLED | new worktree/olean-path failure mode |

### Q1: `is_strictly_sorted` (EASY) — ✅ 0.30s

Flag-fold loop over array; bench derived from `is_sorted`
with `<=` → `<`. Pure Z3 path, no Lean dispatch. Trivial
authoring exercise — confirms the EASY path is now boringly
reliable.

### Q2: `histogram_3buckets` (MEDIUM) — ✅ 68.3s

Single-loop SB(n=3) body classifying `A[k]` into
negative/zero/positive with three tallies. Axiom-heavy with
three case-split UFs. Took **3 attempts** for the agent to
converge:
1. **Attempt 1** (`.solved.lean` cache alone) — wedged at
   ~300 enumerated subsets because partial-subset
   dispatches didn't match the cache's full-τ hashes.
2. **Attempt 2** (HelperRegistry with `import
   SynthLean.Basic`) — timed out at 15s per dispatch under
   the cold-mathlib load.
3. **Attempt 3** (HelperRegistry with `import
   SynthLean.Core` + coverage helper) — **verified in
   68.3s**.

This iteration story is the BEST possible validation of the
F-fixes:
- F4's "`.solved.lean` is preferred" steered the agent
  toward the cache path FIRST (the right default).
- F6's Core/Basic distinction was the dispositive lever for
  closing the run.
- F7's wedge bump prevented giving up early during attempt
  1's enumeration.
- F9's cache-first reorder kept attempt 1's wedge cost
  bounded.

### Q3: `count_pairs_equal` (HARD) — ❌ STALLED

Nested-loop UF accumulation pattern. Agent fully authored
the benchmark + 5 Tier-2 helpers; smoke-tested each helper
individually via `verify_class_via_lean` (all 5 pass with
`via_helper=True` in ~4.5s each); but the **integrated
synth wedged** with a Lean build error: `lake env lean`
resolved `Helpers.olean` at the **CANONICAL** path
(`/Users/saurabh/code/synthesizer/lean/.lake/...`) instead
of the worktree's actual location, even though
`LEAN_PATH` from a fresh subprocess returned worktree
paths.

**Hypothesized root cause:** rsync'd `.lake/build/`
contamination — the agent (reasonably) `rsync`'d the
canonical `.lake/` into the worktree to skip a 30+ min
mathlib rebuild, but `.trace` files inside `.lake/build/`
carry canonical absolute paths that lake's incremental
build then honors. Force-rebuilding the specific Helpers
olean did NOT resolve.

**Three new findings worth surfacing:**
1. **`matches` is a Lean keyword** — UF names need to avoid
   it (and any other reserved word). Worth a quick check
   in `synth/lean_backend/codegen.py`.
2. **`hyp_for` in `HelperRegistry` doesn't know about the
   chain-aware translator's binder prefixes**
   (`h_enc_tau_*`, `h_i1_L1_tau_*`) — these have to be
   hardcoded in the cite-function string. A small API gap;
   could either lift binder discovery into `hyp_for` or
   document the binder shapes in `problem.skill`.
3. **`SETUP.md` §8's worktree note covers stale-venv
   path-resolution, but NOT `.lake/build/` rsync
   contamination.** The "skip mathlib rebuild via rsync"
   shortcut is tempting and unsafe; either we document the
   safe form (rsync only the mathlib oleans, not the
   project build), or we add a worktree-aware `lake clean`
   pre-step.

---

## Synthesis

### What works for an outside agent (today)

- **EASY benchmarks** are now boringly reliable: pure-Z3
  problems derived by copying an existing pattern complete
  in well under a minute with no Lean involvement.
- **MEDIUM axiom-heavy benchmarks** are reliable if the
  agent follows REC 11.6's `.solved.lean` path and uses
  `SynthLean.Core` for the helpers.
- **The mathlib-warm-up + cache-first reorder + Core
  migration** trio (F1+F6+F9) was the dispositive
  intervention; without them, MEDIUM benchmarks under
  parallel contention stall hard.

### What's still rough

- **Multi-agent worktree contention with Lean**: the v3 Q3
  failure is a real, repeatable problem. Any outside
  contributor who tries the "rsync the .lake dir to skip
  mathlib rebuild" shortcut will hit it. Documented now in
  this report; should also land in `SETUP.md` §8.
- **HARD benchmarks** (nested-loop UF accumulation,
  recursive-UF step axioms) still require coaching from
  someone who's seen Slice 2.B / 2.C / Gale-Shapley. The
  helper-citation API gaps (item #2 above) trip even
  careful agents.
- **The codegen module path for the HelperRegistry
  workflow** (vs `.solved.lean` cache) is a separate
  research direction with its own open work (FW E2E + 3
  ports). Outside contributors should stick to
  `.solved.lean` cache for now.

### Next interventions to consider

The three v3-surfaced interventions (F10+F11+F12) shipped
before v4 and are now part of main:

1. ✅ **F10** — `SETUP.md` §8 now documents the safe
   worktree mathlib-rebuild shortcut and the rsync trap to
   avoid.
2. ✅ **F11** — `hyp_for(hole_id, orig_idx, *, role=...,
   chain_k=...)` derives `h_enc_tau_*` /
   `h_i<k>_<lid>_tau_*` prefixes without hardcoding.
3. ✅ **F12** — `Problem.__post_init__` raises early on
   Lean-reserved UF names.

The remaining open question — does F10+F11 actually unblock
HARD chain-aware benchmarks under multi-agent contention?
— wasn't answered by v4 because Q3 wedged for unrelated
reasons. A v5 round with another HARD chain-aware
benchmark would close that loop; lower priority than the
in-flight FW E2E codegen work.

---

## Round v4 — 2026-06-08 (late evening)

**Branch:** `community-validation-v4` (merged: cv-v4-q1,
cv-v4-q2; cv-v4-q3 abandoned)
**Lineup:** EASY + MEDIUM + HARD (3 agents, 60-min budget each).

| Agent | Benchmark             | Difficulty | Outcome   | Wall   |
| ---   | ---                   | ---        | ---       | ---    |
| Q1    | `is_constant_array`   | EASY       | ✅ 0.26s  | pure Z3; pattern-clone of `is_sorted`/`all_positive` |
| Q2    | `find_min_or_zero`    | MEDIUM     | ✅ 1.2s   | pure Z3; agent picked direct-quantifier over UF |
| Q3    | `find_min_max_two_pass` | HARD     | ⚠️ ABANDONED | model-side wedge mid-run; no lessons banked |

### Q1: `is_constant_array` (EASY) — ✅ 0.26s

Flag-fold loop over array. Agent read README + `is_sorted` +
`all_positive`, did NOT need `problem.skill` at all — the two
reference benchmarks were sufficient templates. EASY-tier
pattern-cloning is boringly reliable.

### Q2: `find_min_or_zero` (MEDIUM) — ✅ 1.2s

Conditional min-or-zero. Agent's task prompt suggested
UF + axiom (echoing the framework's axiom-heavy
expectation), but agent found `array_min_val.py` which
proves direct-quantifier τ atoms work fine on Z3, and
composed it with `all_positive`'s flag-disjunction
pattern. **No UFs, no axioms, no Lean dispatch — 1.2s
pure Z3.**

Docs gap surfaced: the agent's reading order
(`min_array` → `min_max_pair` → `array_neg_count` →
problem.skill REC 11 → reference benchmarks) suggests
problem.skill needs a "consider direct-quantifier τ
first; only promote to UF when Z3 wedges" REC.

### Q3: `find_min_max_two_pass` (HARD) — ⚠️ ABANDONED

Designed to exercise F10 (worktree rebuild) + F11
(chain-aware `hyp_for`) + F12 (UF keyword check) under
realistic conditions. Agent created a worktree-local
`.venv-local/` (good — followed SETUP.md §8 correctly),
then began reading reference patterns (transcript shows
it was reading `benchmarks/stretch/merge_two_sorted.py`),
then went silent for 1h 40m: no transcript activity, no
python/lake/lean processes, no benchmark file created,
no commits.

Stopped manually. **No lessons banked from this run** —
the wedge pattern (silent stop after a Read tool result,
no processes) is characteristic of a model-side
infrastructure issue, not a project-side gap. Whether
F10+F11 would have unblocked this HARD benchmark
remains an open question for a future v5 round.

---

## Round v5 — 2026-06-08 (overnight)

**Branch:** `community-validation-v5` (merged: cv-v5-q1,
cv-v5-q2, cv-v5-q3)
**Lineup:** MEDIUM + MEDIUM + HARD (3 agents, 60-min
budget each).  Both MEDIUMs chosen to force axiom-heavy
Lean dispatch — no direct-quantifier escape hatch.

| Agent | Benchmark                | Difficulty | Outcome  | Wall    |
| ---   | ---                      | ---        | ---      | ---     |
| Q1    | `range_sum`              | MEDIUM     | ✅       | 173.3s  |
| Q2    | `sum_pairs_max`          | MEDIUM     | ✅       | 539.4s  |
| Q3    | `find_min_max_two_pass`  | HARD       | ✅       | 0.72s   |

**3/3 verified.**  Total wall: ~12 minutes.  All used
the `.solved.lean` cache path (Path A); none needed
`HelperRegistry`.

### Q1: `range_sum` (MEDIUM) — ✅ 173.3s

Two-bound parametric sum `result = A[l] + … + A[r-1]`.
Generalized `sum_first_k`'s single-bound `k` to a `[l, r)`
range UF named `rsum`.  3-atom τ
(`l ≤ i`, `i ≤ r`, `result = rsum(A, l, i)`) plus 2
recurrence axioms (parametric base + parametric step).
Two `.solved.lean` companions (sc0 entry + sc4
chain-bundle-post).

### Q2: `sum_pairs_max` (MEDIUM) — ✅ 539.4s

`Σ max(A[k], B[k])` via Loop + SB(n=2) branching on
`A[i] >= B[i]`.  Two-array UF `summax` with 3 axioms
(base + per-branch recurrence).  One curated
`.solved.lean` for sc7 chain-bundle-post.  The 9-minute
wall time is dominated by per-subset Z3 enumeration (15s
timeouts on partial-τ subsets that are genuinely
unprovable), not by Lean proof effort.

### Q3: `find_min_max_two_pass` (HARD) — ✅ 0.72s

Two sequential single-pass loops computing min and max.
Template: `SB >> Loop(SB(n=2)) >> SB >> Loop(SB(n=2)) >> SB`.
Both loops carry quantified-prefix τ atoms; the
conjunctive post is discharged from both loops' exit
invariants.  **No UFs, no axioms, no Lean dispatch.**

This was designed to exercise the chain-aware translator
+ F11 `hyp_for(role='enc')`.  The translator's chain-aware
path engaged correctly, but Z3 closed the safety
obligations directly — `h_enc_tau_*` never surfaced
because no helper was needed.

A useful by-product: this benchmark is now the smallest
two-sequential-loops exemplar in the corpus.  Previously
`benchmarks/stretch/merge_two_sorted.py` (three loops,
UF + axioms + helpers) was the only chained-Loop
reference, which set a misleading complexity floor for
authors.

### Findings banked from v5

Eight distinct documentation / UX gaps surfaced.  None
are blockers — all three benchmarks landed verified — but
they're real friction for outside contributors and the
next set of F-fixes:

**From Q1 (`range_sum`):**

1. **Worktree ↔ canonical `lean/` dataflow undocumented
   for the `.solved.lean` path.**  `SETUP.md` §8 covers
   the venv side but not the corollary: `_LEAN_DIR` is
   canonical, so `cwd=_LEAN_DIR` during dispatch means a
   *relative* `dump_lean_failures_dir` resolves against
   the worktree CWD (where `.solved.lean` companions
   land) yet the typecheck runs in canonical's lake env.
   Works correctly but the dataflow is non-obvious; the
   agent had to grep `_LEAN_DIR`/`_typecheck`/`dump_dir`
   in `verify.py`.

2. **sc0 entry-bundle UF cliff.**  When an entry-bundle
   obligation involves a UF base-axiom application (not
   pure linear arith), the first dispatch hits cold
   mathlib AND the omega/nlinarith chain can't handle UF
   rewriting — silent 15s timeout, dumps a TIMEOUT
   banner.  REC 11.4 covers the cold-cache trap but
   doesn't connect it to "author the sc0 `.solved.lean`
   upfront for UF entry-bundles."

3. **Per-sc valid-counts vs global UNSAT triage.**  The
   progress log's "32V/9U/6E on sc4" tallies look like
   per-sc closure but the global wedge is about whether
   the union of per-sc valid τ-subsets has a common
   subset.  A debug.skill note on reading per-sc tallies
   would shortcut UNSAT diagnosis.

**From Q2 (`sum_pairs_max`):**

4. **Z3 enumeration is the wall-clock bottleneck, not
   Lean proof time.**  9 minutes total, all in per-subset
   Z3 enumeration with 15s UNKNOWN timeouts on partial-τ
   subsets.  REC 11.4 mentions cold cache but the real
   cost in steady state is the enumeration treadmill.

5. **`.failed.lean` dumps from partial-τ subsets are
   EXPECTED, not actionable.**  Authors waste time
   reading sc2 dumps that say "i ≥ 0 is missing" and
   trying to prove them — only the full-τ failures
   matter.  No doc note covers this.

6. **The "1 attribute-class returned 'unknown' and were
   rejected" hint is critical but un-localized.**  The
   hint told the agent SOMETHING globally blocked SAT
   but not WHICH (constraint, subset).  Cross-referencing
   failure dumps + dispatch counters took several
   minutes.

7. **`dump_lean_failures_dir` resolves CWD-relative.**
   Must run from worktree root for `.solved.lean` to be
   visible.  `SETUP.md` §6 ("each benchmark is
   self-executable") doesn't note this CWD dependency
   for cache lookup.

**From Q3 (`find_min_max_two_pass`):**

8. **Block-ID assignment ordering needs a worked
   example.**  The agent had to read `synth/ir.py` to
   confirm B0..B4 increment strictly in source order
   across both top-level SBs and nested SBs.  The
   docstring is clear but a multi-SB-multi-Loop chain
   example in `problem.skill` would shortcut the
   exploration.

(There's a 9th candidate: a sequential-Loop reference
benchmark gap — Q3 noted that `merge_two_sorted` was the
only chained-Loop example and it's over-complex.  But
this is resolved by Q3 itself now being in the corpus.)

---

## Round v6 — 2026-06-09 (overnight)

**Branch:** `community-validation-v6` (merged: cv-v6-q1,
cv-v6-q2, cv-v6-q3)
**Lineup:** MEDIUM + MEDIUM + HARD (3 agents, 60-min
budget each).  Same pattern as v5, picked to keep
exercising axiom-heavy + chain-aware paths.

| Agent | Benchmark                | Difficulty | Outcome | Wall    | Lean? |
| ---   | ---                      | ---        | ---     | ---     | ---   |
| Q1    | `count_two_arrays_equal` | MEDIUM     | ✅      | 873.5s  | yes (6 `.solved.lean`) |
| Q2    | `cumulative_max`         | MEDIUM     | ✅      | 580s    | no (pure Z3) |
| Q3    | `sum_two_passes`         | HARD       | ✅      | 1240s   | yes (4 `.solved.lean` w/ chain-aware binders) |

**3/3 verified.**  Notable: Q3 is the **first** HARD chain-
aware benchmark to actually exercise F11's chain-aware
binder prefixes (`h_i<k>_<lid>_tau_*`).  Three prior HARD
attempts (v3 Q3 STALLED on worktree-olean bug, v4 Q3
ABANDONED on model wedge, v5 Q3 closed pure-Z3) didn't
hit the chain-aware Lean dispatch path.  Q3's
`sum_two_passes` (sum UF + recurrence axioms forcing Lean)
landed there cleanly.

### Q1: `count_two_arrays_equal` (MEDIUM) — ✅ 873.5s

Two-array case-split counter — lifted `count_zeros` /
`count_equal` to a two-array UF `count_eq2(A, B, k)` with
3 axioms (base + matching-case increment + non-matching
identity).  3-atom τ (`c == count_eq2(A,B,i)`,
`0 ≤ i ≤ n`).  Agent hand-curated 6 `.solved.lean`
companions covering full-τ (4-of-4) and {0,1,2} (3-of-4)
subsets for sc2 / sc4 / sc7.  F17, F19 fired correctly;
F18 didn't (no NoSolution).

Strategy worth banking: agent **pre-authored** multiple
candidate `.solved.lean` files (full-τ + likely smaller
subsets) using a Python hash-computer script, lifting
proofs verbatim from `count_equal`'s solved companions with
mechanical `B i` substitution for `t`.

### Q2: `cumulative_max` (MEDIUM) — ✅ 580s

Output array `C[k] = max(A[0..k])` via single loop +
SB(n=2) updating `C[i]` and running `m` in parallel.
Bilateral quantifier τ (universal `∀k<i. A[k] ≤ m` +
existential `∃k<i. A[k] = m`, lifted to the C array as a
second pair) — 6 atoms, pure Z3 closed every obligation.
No UFs.

Tractability cliff data: ~244s of the run was sc7's
safety-bundle-post burning UNKNOWN sweeps before
resolving.  REC 1's "9+ atoms = minutes" guidance is
slightly conservative; 6 atoms with bilateral nested
quantifiers over Store/Select reach the cliff.

### Q3: `sum_two_passes` (HARD) — ✅ 1240s — **first true F11 exercise**

Two sequential single-pass loops accumulating into
`result`: L0 sums A, L1 continues into the same accumulator
summing B.  Template `SB(B0) >> Loop(L0) >> Loop(L1)`.
UF `sum(A, k)` + recurrence axioms → Lean dispatch forced
(Z3 can't decide quantified UF equality).

The L1-entry obligation (sc4) and chain-bundle-post (sc8)
go through the chain-aware translator.  Agent authored 4
`.solved.lean` files using F11's chain-aware binder
patterns:

- `h_i0_trans_*` for B0's init transition.
- `h_i1_L0_tau_*` for L0's abstract transition (chain item
  index 1).
- `h_i2_L1_tau_*` for L1's abstract transition (chain item
  index 2).

Agent used `hyp_for` semantics implicitly via the
translator-dumped binder names; did NOT need `role='enc'`
(no nested loop), did need `chain_k` semantics (Loop items
in chain prefix).  F11 finally validated end-to-end.

### Findings banked from v6

Q3 surfaced 4 new candidates worth tracking; Q1 added 3
more.  None are blockers (3/3 verified); these are
next-round F-fix candidates.

**From Q3 (`sum_two_passes`):**

1. **`python -c` vs `python script.py` resolve `_LEAN_DIR`
   differently.**  `-c` puts CWD as `sys.path[0]`; if a
   `synth/` dir exists in CWD (worktree root), Python
   imports the worktree's stub-synth → `_LEAN_DIR` points
   at a broken worktree lean dir.  `python benchmarks/*.py`
   puts `benchmarks/` (not CWD) in `sys.path[0]`, so the
   editable install resolves correctly.  Agent spent ~10
   min diagnosing this.  SETUP.md §8 should call out the
   asymmetry.

2. **`[PROGRESS]` dispatch counts are GLOBAL accumulators
   even though the axiom-heavy path uses LOCAL counters
   until fold-back.**  During sc4 / sc8 enumeration the
   printed counts froze for ~7 min (22V/9U/4E plateau),
   making the run look wedged.  Counts only updated at
   end-of-sc fold-back.  Adding per-sc local-counter
   snapshot to PROGRESS would prevent false-wedge concerns.

3. **F17 partial-τ infix only considers the CURRENT loop's
   τ.**  sc8 dumps have `loop_id=L0` (via atom_ref
   fallback) so the `_partialNofM_` infix tracks τ@L0.
   But sc8's chain hyps include τ@L1 (from L1's abstract
   transition), and the τ@L1 subset varies independently.
   16 sc8 dumps had `loop_id=L0` "full-τ" naming but only
   2 were actually full-τ@L1.  Extension: infix all τ
   holes involved, e.g. `_L0_3of3_L1_2of3_`.

4. **`.solved.lean` cardinality explodes for chain-aware
   HARD benchmarks.**  Q3 had τ@L0×τ@L1 = 2^3×2^3 = 64
   possible subset combinations for sc8 alone, each with
   a unique signature hash.  REC 11.6 should recommend
   `HelperRegistry` (one helper covering all 64 variants
   via per-subset enumeration) for chain-aware HARD,
   sidestepping the cardinality explosion.

**From Q1 (`count_two_arrays_equal`):**

5. **`_consult_companions` typechecks every cache hit
   (~2–3s via `lake env lean`).**  With many subsets, this
   accumulates linearly.  Could short-circuit with a
   filename-existence check + a hash-based trust mode
   (lossier but faster) for repeated runs of the same
   benchmark.  Soundness tradeoff: the typecheck guards
   against stale companion content.

6. **No per-VALID logging — authors can't see which τ
   subsets are passing.**  Partial-τ dumps appear late;
   full-τ may never appear if Z3 closes most subsets.
   Suggested: `[INFO] sc<idx> valid τ subset = atoms
   {...}` per VALID dispatch.

7. **Pre-authoring `.solved.lean` candidates for
   likely subsets is a useful strategy.**  Q1's agent
   wrote a Python script to compute hashes for several τ
   subsets up-front, then lifted proofs from a reference
   benchmark verbatim with mechanical substitution.  This
   should be documented in REC 11.6 as the canonical
   onboarding pattern for new MEDIUM benchmarks
   resembling existing ones.

(Triage 2026-06-09: F21–F27 are all good-to-have, none
needed for successful solving — v6 was 3/3 verified without
them.  Banked but not shipped.  Wait for them to actually
bite an agent in v7+ before investing.)

---

## Round v7 — 2026-06-09

**Branch:** `community-validation-v7` (merged: cv-v7-q1,
cv-v7-q2, cv-v7-q3)
**Lineup:** MEDIUM + HARD + HARD with explicit
NEW-ALGORITHMIC-TYPE constraint — picked patterns
intentionally distinct from prior rounds' counters / sum
UFs / case-split counters / cumulative arrays / two-loop
chains.

| Agent | Benchmark              | Difficulty | Outcome | Wall    | Notes |
| ---   | ---                    | ---        | ---     | ---     | ---   |
| Q1    | `has_adjacent_equal`   | MEDIUM     | ✅      | 0.2s    | pair-of-consecutive flag-fold; pure Z3 |
| Q2    | `suffix_sum`           | HARD       | ✅      | 290.9s  | right-to-left scan; 3-arg UF; 5 `.solved.lean` |
| Q3    | `matrix_diagonal_sum`  | HARD       | ✅      | 128.0s  | first agent-authored 2D benchmark; UF + axiom |

**3/3 verified.**  Total wall: ~7 minutes.  This is the
first round to explicitly target algorithmic-type diversity
rather than just difficulty tier — all three patterns are
new to the post-v1 community-validation corpus.

### Q1: `has_adjacent_equal` (MEDIUM) — ✅ 0.2s

Pair-of-consecutive flag-fold: return 1 if
`∃k. 0 ≤ k < n-1 ∧ A[k] == A[k+1]`, else 0.  Agent ported
`is_sorted`'s pattern to the existential-dual: flag
initialized to 0 (no witness seen), set to 1 on
observation.  Single τ atom with universal-OR-existential
disjunction.  Pure Z3, no Lean.

Distinct from prior flag-folds (`is_sorted`,
`all_positive`, `is_constant_array`, `is_strictly_sorted`)
because the predicate examines pairs of consecutive
elements rather than single elements.

### Q2: `suffix_sum` (HARD) — ✅ 290.9s

Right-to-left cumulative array: `C[k] = A[k] + A[k+1] +
... + A[n-1]`.  Template `SB() >> Loop(SB(n=2))`: init
`i := n`, then SB(n=2) branches on first-write
(`i = n`, base case) vs propagate-leftward (`i < n`,
recursive case).  3-arg UF `sum_suffix(A, k, m)` with
right-to-left recurrence axiom.  5 `.solved.lean` files.

Direction-flip from `prefix_sums` worked once the SB(n=2)
shape was chosen: `phi = i` decreasing to 0, loop guard
`i > 0`, ranking-lb derived from atom `0 ≤ i`.  Store
transitions `Update(C, i - 1, ...)` parsed cleanly.

### Q3: `matrix_diagonal_sum` (HARD) — ✅ 128.0s

First agent-authored 2D benchmark beyond `matrix_init`.
Single loop `i: 0..n-1` accumulating `A[i][i]` into
`result`.  UF `diag_sum(A, n, k)` with base + recurrence
axioms, identical structure to `sum_array` but with 2D
array indexing.

Key validation: **2D atom strings work transparently**.
`A[i][i]` parses cleanly through Z3 (nested `Select`) and
Lean (`(A k) k`).  UF arg-type `int[][]` auto-parenthesizes
to `(Int → Int → Int)`.  No special escaping needed.  The
2D framework extension (Phase 3.S) is real and
agent-accessible.

### Findings banked from v7

Three of the findings (F28+, below) are real authoring
footguns rather than diagnostic-quality items.  But per
the v6 triage rule (ship docs only when verified
necessary), none of these blocked the v7 agents from
landing 3/3 verified — they're banked, not shipped.

**From Q2 (`suffix_sum`):**

1. **Ranking obligations are Lean-cache-only.**
   `synth/solver.py` (`_ranking_kind`) treats
   ranking-lb / ranking-decrease as cache-only — generic
   tactic chain is skipped.  Consequence: on cache MISS,
   no `.failed.lean` is dumped, so authors can't iterate
   against a dump file.  The Q2 agent had to compute the
   sc6 signature hash by calling `theorem_for_ranking_lb`
   + `_signature_hash` directly via Python.  REC 11.7.A
   could document this recipe.

2. **Right-to-left UF axiom needs explicit index-shift
   rewrite.**  The right-to-left recurrence `∀k. k < m →
   sum_suffix(A, k, m) = A[k] + sum_suffix(A, k+1, m)`
   instantiates at `(i-1)+1 = i`, but Lean doesn't
   simplify arithmetic inside UF args automatically.  The
   author needs an explicit `have h_idx : (i-1)+1 = i :=
   by omega` step before the `rw [user_axiom_1]`.
   problem.skill near REC 11's axiom-recurrence
   guidance could note this pattern for non-standard
   direction loops.

3. **`subst h_g_branch` on `i = n` can delete free
   variables.**  Lean's `subst` deletes the substituted
   name; if the guard equation is `i = n` and `n` is a
   bound variable in the outer theorem, `subst` removes
   the outer binder, leaving downstream `n` references
   broken.  Workaround: keep the hypothesis and use
   `rw [h_g_branch]` instead.

**From Q3 (`matrix_diagonal_sum`):**

4. **2D `rw [← h_i]` over-rewrites when the UF takes the
   index arg twice.**  Q3's first sc4 proof copy-pasted
   `sum_array`'s template `rw [← h_i]; exact h_tau_2`.
   With `h_i : i' = n` and goal `diag_sum A n n`, the
   backward rewrite swapped BOTH occurrences of `n`,
   making the result `diag_sum A i' i'` which doesn't
   match `h_tau_2 : result' = diag_sum A n i'`.  Fix:
   `rw [h_i] at h_tau_2; exact h_tau_2`.  Worth a note in
   problem.skill's chain-aware section: when porting
   sum_array's proof templates to 2D UFs, prefer
   forward-rewrite-at-hyp over backward-rewrite-on-goal.

**From Q1 (`has_adjacent_equal`):**

5. **REC 11.5's universal-gate guidance could explicitly
   cover the existential-dual case.**  Q1's agent
   reverse-engineered the `or k == n - 1` boundary gate
   from `is_sorted` and noticed it was effectively a no-op
   in the existential-dual case (predicate checks
   `A[k] ≠ A[k+1]`, where `k < i ≤ n-1` already implies
   `k ≤ n-2`, making the OR-clause unreachable).  Doc note
   in REC 11.5 about when the gate is load-bearing vs
   vacuous would shortcut the reverse-engineering.

(Of the 5 v7 footguns, F28 was shipped as a 5-line code
fix in `synth/lean_backend/verify.py` — cache-only path now
dumps `.failed.lean` on miss so ranking obligations are
visible to authors.  F29–F32 banked but not shipped.)

---

## Round v8 — 2026-06-09

**Branch:** `community-validation-v8` (merged: cv-v8-q1,
cv-v8-q2, cv-v8-q3)
**Lineup:** HARD + HARD + HARD with explicit "new
algorithmic types" constraint.  Categories chosen:
two-pointer toward middle, self-referential array
recurrence, late-binding witness reduction.

| Agent | Benchmark         | Algorithmic type              | Outcome | Wall    | Lean? |
| ---   | ---               | ---                           | ---     | ---     | ---   |
| Q1    | `is_palindrome`   | two-pointer toward middle     | ✅      | 0.95s   | no (pure Z3) |
| Q2    | `fibonacci_array` | self-referential array recurrence | ✅  | 137.3s  | yes (5 `.solved.lean`) |
| Q3    | `find_max_index`  | late-binding witness (LAST-of-max) | ✅ | 0.93s   | no (pure Z3) |

**3/3 verified.**  Notable: Q2 (`fibonacci_array`) is the
**first** benchmark where the agent had to author 5
`.solved.lean` files spanning multiple bundle obligations
in one go, including discovering the framework's
chain-aware vs non-chain dispatch overlap (see findings
below).

### Q1: `is_palindrome` (HARD) — ✅ 0.95s

Two-pointer scan toward middle: `i := 0; j := n-1`; in
each iteration compare `A[i]` and `A[j]`, advance
`i++; j--`; terminate when `i >= j`.  Agent ported
`reverse_array`'s two-pointer pattern; key adaptations:
- Ranking `phi = j - i + 1` (not `n - i`); the `+1` keeps
  it ≥ 0 at the n=0 entry state where `j = -1`.
- Atom `i + j == n - 1` is load-bearing — it couples the
  pointers so the τ flag-fold can use a *prefix-only*
  quantifier (range `[0, i)`) and still entail the full
  symmetric `∀k. 0 ≤ k < n → A[k] = A[n-1-k]` post at exit.
- Atom `i <= j + 1` is the ranking-lb invariant.

### Q2: `fibonacci_array` (HARD) — ✅ 137.3s

Output array `C[k] = fib(k)` via self-referential
recurrence.  Init SB writes both base elements
(`C[0] = 0, C[1] = 1`) in one parallel assignment with
nested `Update(Update(C, 0, 0), 1, 1)`, then loops
`i: 2..n-1` with `C := Update(C, i, C[i-1] + C[i-2])`.
UF `fib` with 3 axioms; τ@L0 = `{2 ≤ i, i ≤ n, ∀k. 0 ≤ k < i → C[k] = fib(k)}`.
5 `.solved.lean` files cover sc0 (entry), sc1 (loop
inductive), sc4 (chain-bundle post) — and importantly
TWO variants of sc0 + sc4 each (see Finding 2 below).

### Q3: `find_max_index` (HARD) — ✅ 0.93s

LAST index of max via late-binding witness.  Agent
cloned `array_max_index` and flipped `>` to `>=` in the
branch guard (a 2-character edit).  τ uses bilateral
universal atoms: `(∀k. 0 ≤ k < i → A[k] ≤ m) ∧ (∀k. idx < k < i → A[k] < m)`.
Branch 0 (idx jumps to i) trivially re-establishes the
strict-< clause (the strictly-after range `idx_new < k < i+1`
is empty since `idx_new = i`); branch 1 extends it.  Pure
Z3 closed everything in <1s.

Prescriptive nugget: the canonical encoding for "LAST
occurrence" benchmarks is **(weak-≤ over whole prefix) ∧
(strict-< over strictly-after-witness range)**.  The
strict-< over a vacuous post-update range is what keeps
the invariant inductive.

### Findings banked from v8

Q2 surfaced two genuinely surprising findings; Q1 and Q3
each surfaced one minor prescriptive nugget.

**From Q2 (`fibonacci_array`) — both worth examining beyond
"nice-to-have":**

1. **Worktree lake build cold-start blew the budget.**
   The worktree had an empty `lean/.lake/build`; running
   `lake build SynthLean.Basic` started a full mathlib
   compile (8062 oleans, projected ~50 min) that would
   have overrun the 60-min budget.  Agent's manual fix:
   symlink the worktree's
   `lean/.lake/packages/mathlib/.lake/build` to the
   parent repo's already-built dir.  After symlink,
   `lake build SynthLean.Basic` finished in 11s.
   **SETUP.md §8 / lean/setup.sh should symlink mathlib
   build dir into worktrees by default** — this is a
   30–50 min budget destroyer for any worktree user.
   (v3 Q3 hit a related issue with rsync contamination;
   this is the missing positive recipe.)

2. **Dual-dispatch on bundle obligations.**  The
   framework's translator emits BOTH
   `theorem_for_entry_bundle` AND
   `theorem_for_entry_bundle_chain` for the same
   `safety-bundle-entry` constraint, producing two
   distinct signature hashes.  Q2 had to author 2
   `.solved.lean` files for sc0 + 2 for sc4 = 4 of the
   5 total companions, just to cover the dual-dispatch.
   The prior chain-aware benchmark (v6 Q3
   `sum_two_passes`) didn't expose this because its
   chain has `[B0, L0, L1]` with two Loops — the chain
   detection unambiguously routes to `_chain` variant
   only.  Q2's shape `SB(B0) >> Loop(L0)` has only one
   SB before the loop, which triggers BOTH dispatches
   (translator picks based on chain heuristic, but
   per-class enumeration also independently dispatches
   the non-chain variant).  Looks like a real bug:
   either the chain detection is over-firing, or the
   solver is double-dispatching the same obligation
   through both translator paths.  Worth investigating
   in `synth/lean_backend/verify.py:166-191` (the
   `_use_chain` gate).

**From Q1 (`is_palindrome`):**

3. Two-pointer ranking `j - i + 1` (not `n - i`) and the
   `i + j == n - 1` coupling atom are non-obvious to
   first-time authors.  Both derive from `reverse_array`
   if you study it carefully, but a one-line REC pointer
   would shortcut the inference.  Marginal — agents are
   figuring it out.

**From Q3 (`find_max_index`):**

4. The (weak-≤ whole-prefix) ∧ (strict-< strictly-after)
   encoding for "LAST occurrence" patterns is the
   bilateral analog of REC 2 / REC 5.  Worth a sentence
   if a second LAST-occurrence benchmark surfaces in
   the corpus.

**From Q2 (additional minor — not promoted):**

5. SSA-list init transitions are rejected by the
   chain-aware bundle translator with
   `NotImplementedError: chain-item SB: non-dict atom`.
   Agent worked around by collapsing into one parallel
   `Update(Update(...))`.  Either real fix (lift SSA
   support into the chain translator) or clearer error
   message would help.

6. `ring` is not in `SynthLean.Core`; `omega` works.
   problem.skill REC 11.8's Core-tactic list could
   explicitly call out the absence.

7. `simp [store, h_eq]` doesn't always close
   store-transparency goals.  Workaround:
   `have h_store_off : store C i v k = C k := by simp [store, h_eq]; rw [h_store_off]`.
   A `store_off` lemma in `SynthLean.Core` would
   eliminate the workaround.

---

## Code shipped during this audit

| Commit  | Round | Description |
| ---     | ---   | ---         |
| `bc8f8c7` | v1→v2 prep | F1–F5: setup + collision check + skill prefs + lesson |
| `2948f0c` | v2→v3 prep | F6+F7+F9: Core migration + wedge bump + cache-first |
| `22b1950` | v3 Q1 | `is_strictly_sorted` benchmark |
| `4ac838d` | v3 Q2 | `histogram_3buckets` benchmark + helpers |
| `165ae56` | v3 Q3 | `count_pairs_equal` (STALLED — diagnosis only) |
| `a949c3d` | v3→v4 prep | F10+F11+F12: worktree docs + `hyp_for(role=...)` + UF keyword check |
| `6fdb787` | v4 Q1 | `is_constant_array` benchmark |
| `f71debc` | v4 Q2 | `find_min_or_zero` benchmark |
| `52b2187` | v5 Q1 | `range_sum` benchmark + 2 `.solved.lean` companions |
| `3d46645` | v5 Q2 | `sum_pairs_max` benchmark + 1 `.solved.lean` companion |
| `6c0ceb9` | v5 Q3 | `find_min_max_two_pass` benchmark |
| `8e4370f` | v5→v6 prep | F13–F20 (8 fixes from v5 friction audit) |
| `961a5c8` | v6 Q1 | `count_two_arrays_equal` benchmark + 6 `.solved.lean` |
| `ca9c9a7` | v6 Q2 | `cumulative_max` benchmark |
| `2214e75` | v6 Q3 | `sum_two_passes` benchmark + 4 chain-aware `.solved.lean` |
| `732d104` | v7 Q1 | `has_adjacent_equal` benchmark (pair-of-consecutive flag-fold) |
| `b6fe514` | v7 Q2 | `suffix_sum` benchmark + 5 `.solved.lean` (right-to-left) |
| `ff41a2b` | v7 Q3 | `matrix_diagonal_sum` benchmark + 1 `.solved.lean` (2D) |
| `6fafed3` | v7→v8 prep | F28: dump `.failed.lean` on ranking-cache-miss |
| `09b7f31` | v8 Q1 | `is_palindrome` benchmark (two-pointer toward middle) |
| `d7487d3` | v8 Q2 | `fibonacci_array` benchmark + 5 `.solved.lean` (self-referential) |
| `f6e7836` | v8 Q3 | `find_max_index` benchmark (late-binding witness) |

All eight round branches (`community-validation`,
`community-validation-v2`, …, `community-validation-v8`)
live on the remote.

---

## Reproducibility

Each round followed the same protocol:
1. Spawn N general-purpose subagents in parallel, each on
   its own `/tmp/agent-vX-pN` git worktree on a fresh
   branch.
2. Each agent's prompt: "you're a fresh Claude with no
   prior context; read the docs index in README.md; pick
   the path that fits; ship one verified benchmark in
   ≤60 min; commit + return".
3. Wait for all agents to return; merge each branch into
   the round's integration branch; analyze failures; bank
   findings as F-numbered fixes; ship the fixes to main
   before the next round.

The full agent transcripts are in the harness task logs
under `/tmp/claude-501/.../tasks/<task-id>.output`.
