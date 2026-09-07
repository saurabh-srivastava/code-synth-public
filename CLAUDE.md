# Synthesizer — project context

## Repo layout — what lives where

| File | Audience | Purpose | Auto-refresh |
| --- | --- | --- | --- |
| `README.md`             | public               | Public landing: pitch + north stars + quick-start + status + docs index + license | every phase |
| `LICENSE`               | public               | GPL-3.0-or-later text | — |
| `CITATION.cff`          | public               | Academic citation metadata | — |
| `CONTRIBUTING.md`       | contributors         | Phase-completion routine + subagent prompt template + experience-report rule + code style | per process change |
| `PRINCIPLES.md`         | implementer + LLM    | Governing principles (P-1..P-4), always-on reminders (A-1..A-4), north-star expansions (NS-1..NS-3) | when a principle is banked |
| `CLAUDE.md`             | implementer (Claude) | Session TL;DR: repo layout + most-recent ~3 phases + locked decisions + pointers | per phase |
| `CHANGELOG.md`          | implementer + future | Phase-by-phase history (everything older than the most recent ~3 phases) | per phase |
| `DESIGN.md`               | implementer          | Algorithm / IR / encoding design doc (§2 inputs, §3 framework, §4 DSL, §5 constraint encoding, §6 decoding, §7 hurdles).  Phase log moved to CHANGELOG; north stars to README; paper summaries to ref/PAPERS. | rare (design rationale) |
| `SOUNDNESS.md`          | impl + public        | Soundness posture: what "verified" means + safety nets | when verifier pipeline changes |
| `BENCHMARKS.STATUS.md`  | impl + public        | Per-benchmark catalog organized by tier (canonical "what's verified") | every phase / per benchmark |
| `EXPERIENCE_REPORT.md`  | public (long form)   | Case studies on Claude as research assistant — verbose by design | ad-hoc, on case study |
| `problem.skill`         | LLM driver           | Happy-path guide for authoring a `Problem` | every phase |
| `debug.skill`           | LLM driver           | What to do when something goes wrong | every phase |
| `RESEARCH.md`           | impl + future        | Post-foundations research threads (NL → Problem; Lean backend; perf; HumanEval triage; Claude Suggested Directions §O) | infrequent |
| `RESEARCH.COMPLETED.md` | impl + future        | Archived completed research design passes (§K.B / §K.B-REVIEW / §K.D) | when a research thread ships |
| `RESEARCH.LEAN.md`      | impl                 | Lean backend specifics + Ring 1 end-of-MVP review | when Lean capability changes |
| `OPEN_PRBS.md`          | impl + future        | Catalog of open problems (Karatsuba GF(2^k), sub-cubic min-plus matmul, etc.) | when an item is promoted |
| `COST_INVS.md`          | impl + future        | Design plan for cost-bound invariants (NS-1 substrate) | when cost-inv infra progresses |
| `HUMANEVAL.STATUS.md`   | impl + future        | Triage of 164 HumanEval+ problems on 5-level rubric | when framework extensions shift ratings |
| `NL_FRONTEND.md`        | impl + future        | Parked plan: fine-tuned LLM English → `Problem` driver | when we embark on NL FT |
| `CASE_STUDY.md`         | impl + public        | Self-contained walkthrough of greedy-maximal-bipartite-matching benchmark | rare |
| `ref/PAPERS.md`        | impl                 | POPL'10 / PLDI'11 / PLDI'09 paper summaries + transferable insights | rare |
| `lean/README.md`        | impl                 | Lean project setup, build instructions, troubleshooting | when Lean setup changes |
| `SETUP.md`              | public + new users   | From-scratch install: Python venv, Lean toolchain, sanity-check | when install path changes |

All of these are kept in sync via the **Phase-completion
routine** in [`CONTRIBUTING.md`](./CONTRIBUTING.md).  Read
`DESIGN.md` before making architectural decisions; read
`RESEARCH.md` when thinking about the long-term direction.

## What we're building

A clean-room reimplementation of *Pragna* (POPL'10 + PLDI'11). Consumes
`(control-flow template, predicate space, spec)` and produces `(code,
proof)`. Eventual pipeline: `NL → LLM → (template, predicates) →
synthesizer → code + proof`. The LLM front-end is out of scope.

## North stars

Canonical statement: [`README.md`](./README.md).
Implementer-facing expansion (NS-1 / NS-2 / NS-3):
[`PRINCIPLES.md`](./PRINCIPLES.md).

Three long-horizon dimensions: (1) resource-bounded
synthesis, (2) module-level synthesis, (3) discovering novel
programs.  The current Phase X/Y work is a **bridge** toward
these north stars, not the destination.  Prefer foundations
that generalize to the north stars over one-off polish.

## Locked decisions (canonical version in DESIGN.md §1.1)

- **Algorithm.** POPL'10 proof-theoretic synthesis over **predicate
  abstraction** (VS3-PA flavour). PINS is a later add-on, not the base.
  LIA / bounded-coefficient search is out of scope.
- **Implementation.** Pure Python + `z3-solver` through Phase 4.
  C and Rust source emitters in Phase 5. MLIR is Phase 6 and **optional**
  — only if it earns its keep after the pipeline works on real examples.
- **DSL.** Ship three surfaces over one IR: Python eDSL (canonical),
  textual (`"SB ; LOOP { SB } ; SB"`), JSON. Spec is strings on the
  `Problem` object.
- **Predicate inference.** Hand-authored for now; the synthesizer
  surfaces UNSAT witness paths + timeout telemetry so the LLM outer
  loop can iterate (`SolveResult | NoSolution | Timeout`, see DESIGN.md §6).
- **Axiom library.** Shipped as a standard library (strings, arrays,
  recursion shapes, trig).
- **PLDI'09 reduction.** Re-derive straight from the paper. No
  speculative refinements.
- **Solution ranking.** Enumerate + sort by `α·atom_count + β·cost_proxy`.

## Current phase

**Phase Fpre-Sym — Fpre propagation symmetry in SB-body fast path (2026-06-08).**
**Code fix — eliminates the Pre-as-τ-atom workaround.**

`synth/constraints.py:emit_loop_body`'s SB-body fast path
built the inductive antecedent as `τ ∧ g_loop ∧ g_branch ∧
trans` WITHOUT `Fpre`.  The recursive-walk path for non-SB
bodies (~line 746) DOES propagate `Fpre`, and so does the
break-branch path right above the bug.  The Lean translator
also already binds `h_pre` for every `safety` /
`ranking-decrease` / `cost-decrement` theorem.  So the Z3
obligation was the lone outlier — stricter than the Lean
obligation it parallels.

**Discovered**: 2026-06-08, by the main-agent during the
docs-reconcile dual-agent regression test on
`saturating_sum`.  The agent had to mirror Pre's nonneg-
elements fact into a τ atom (~quantified) because the
inductive obligation couldn't see Pre.  Banked as
"framework gotcha discovered" in the post-test report.

**Fix**: add `Fpre(body_in)` to `ant_parts` in
`emit_loop_body`'s SB-body fast path (~line 720).  Single
line + comment.  This is a WEAKENING of the obligation
(more antecedents = more hypotheses = more permissive), so:
  - Soundness preserved: any class previously accepted
    stays accepted.
  - Completeness improved: some previously-rejected classes
    may now be accepted (specifically: any class that's
    only valid under `Fpre`).
  - Z3 obligation now matches the Lean obligation's
    hypothesis set (lesson #66 — parity restored).

**Validation**:
- `saturating_sum` WITHOUT the Pre-as-τ-atom workaround
  synthesizes in 0.17s (down from 0.47s with the workaround).
- Quick regression: **72/72 passed**.
- Two benchmarks gained additional sound solutions exposed
  by the weaker antecedent:
  - `mul`: 2 → 4 (τ atoms `0 <= i` and `p >= 0` are now
    provably preserved under Fpre's `a >= 0`).
  - `intdiv`: 2 → 4 (τ atoms `y > 0` and `q >= 0` now
    provably preserved; `max_solutions` bumped from 3 → 5
    to expose the full set).
  Both updates banked as intentional `expected_solutions`
  bumps with inline comments tracing back to this phase.
- Wall-clock spot check on 5 benchmarks: within noise;
  `array_zero` actually faster (40s → 26s, likely because
  Fpre tightens the per-class enumeration's search space).

**Lesson #79 banked**: *Fpre propagation must be UNIFORM
across all body-walk paths.*  The framework had three
paths: (a) recursive-walk for non-SB bodies, (b) SB-body
fast path's break branches, (c) SB-body fast path's normal
branches.  (a) and (b) propagated Fpre; (c) did NOT.  The
inconsistency was a latent bug — visible only when a
benchmark's Pre carries a fact the inductive depends on,
which is unusual but real (saturating_sum's
`∀k. A[k] ≥ 0`).  Workaround was always available (mirror
Pre into a τ atom) but adds an unnecessary 2^|τ|
enumeration factor.  Generalization: any time three+ code
paths handle "the same operation," check that they actually
agree.  Lean translator parity (lesson #66) is the
companion principle.

---

**Phase L1.6 breadth — Gale-Shapley E2E closure (2026-05-28).** 🎯
**MILESTONE — second L1.6 benchmark to ship with FULL Tier-1
proven helpers; recursive-UF step-axiom encoding validated
on a non-matching algorithm.**

`benchmarks/open_prbs/stable_matching/bench_gale_shapley.py`
synthesizes 1 verified solution in **86.1s wall** (merge
commit `d5cf825`).  Mod-cycled Gale-Shapley with 3-branch
SB(n=3) body (SKIP / ACCEPT / REJECT) and a `k_left` budget
counter from `k_iter`.

  - **6/6 Tier-1 PROVEN helpers** in
    `lean/SynthLean/Y2Corpus/gale_shapley/Helpers.lean`:
      - `gs_sc0_entry_l0` (entry-bundle from base axioms).
      - `gs_sc1_coverage` (3-way trichotomy on SB(n=3)).
      - `gs_sc2_skip` (SKIP branch).
      - `gs_sc4_accept` (~170 LOC) — ACCEPT branch with
        multi-case proof on the 4-store mate update; cites
        7 ACCEPT step axioms.
      - `gs_sc6_reject` (~80 LOC) — REJECT branch; mate/wmate
        unchanged (frame eqs); only nxt[m_cur] increments.
      - `gs_sc9_final` (~15 LOC) — bridges loop-exit
        (`k_left' = 0` from `0 ≤ k_left'` + `¬(k_left' > 0)`)
        to the bench's `k_iter` post.
  - **17 step axioms** total (concrete recursive-UF
    semantics):
      - 3 base cases (GSMate/GSWMate/GSNxt at k=0).
      - 1 structural (`gs_nxt_nonneg`).
      - 3 SKIP step axioms.
      - 7 ACCEPT step axioms (A-G).
      - 4 REJECT step axioms (A-D).
  - **NO classical-theorem trust** — bench's post is
    recursive-UF equality at `k_iter`, not GS stability.
    The classical "GS produces a stable matching" theorem
    would be a SEPARATE axiom layered on top.

### Encoding lessons banked from L1.6 breadth (Gale-Shapley)

**76. Axiom-free trust is a first-class goal, even at extra
proof-engineering cost.**  GS could have axiomatized the
per-iteration preservation lemmas as Tier-2 (3-line axioms
per branch).  We chose to prove them as Tier-1 theorems
(170 LOC for ACCEPT alone).  The cost: ~half a day of careful
multi-case proof work.  The win: every algorithm-step
preservation claim in the synthesized solution is verified
in Lean from concrete `store` semantics + step axioms — the
trust surface is *just* the 17 axioms describing what the
algorithm does, with all consequences of those steps proved.
The Slice 2.C → GS pattern: identify the load-bearing
algorithm-step axioms; prove preservation as Tier-1 theorems;
keep only the genuinely-classical axioms (Berge for matching;
recursive-UF base/step for GS) at the bottom.

**77. The mod-cycled k_left budget is the standard fix
for "no nested scan" in iteration-budget algorithms.**
Gale-Shapley's natural shape is "while ∃ free man, propose"
— requires a scan or queue.  Mod-cycling `m_cur` modulo `n`
with a budget counter `k_left = k_iter` reshapes the loop
into a single-pass iteration with a 3-way SB body.  For
k_iter ≥ n², every (free-man, attempt) pair is visited at
least once.  This generalizes: any algorithm naturally
expressed as "while X exists, do Y" can be reshaped to
"for budget iterations: cycle through candidates with mod;
SKIP / DO / continue" — avoiding the nested-loop framework
gap.  The cost is loose iteration count (k_iter vs. exact);
the win is no new IR primitive needed.

**78. Per-helper required_atoms gating eliminates dead-end
subset enumeration.**  GS's τ@L0 has 8 atoms (2^8 = 256
subsets per safety obligation).  Without `required_atoms =
frozenset({0..7})` on the helper entries, the helper
short-circuit only triggers on the FULL subset; smaller
subsets fall through to generic Lean tactic chain (timeout
→ UNKNOWN → sound-mode rejection → ABANDON).  With
`required_atoms` set to the full subset, the helper cite
fires on the FULL subset cube alone, and the synth produces
a valid solution carrying the full τ — score-minimization
gives up a small amount but correctness + termination
landed in 86s instead of wedging.  General rule: when a
helper's proof legitimately requires all τ atoms, declare
the full subset in `required_atoms` to keep enumeration off
the wedging path.

---

**Phase Slice 2.C — max matching with CONCRETE IsMatching +
Tier-1 proven flip-preservation (2026-05-27).** 🎯
**MILESTONE — first L1.6 max-matching benchmark to ship with
REAL Lean proofs for all algorithm-step preservation
lemmas.  Trust tier reduced from 5 axioms (Slice 2.B) to
2 axioms (only Berge + class-restriction).**

`benchmarks/open_prbs/l16_bipartite_matching/bench_max_matching_concrete.py`
synthesizes 1 verified solution in **131.9s wall** (merge
commit `b0c9d63`).  Fork of Slice 2.B's bench, axiom-
tightened to replace UF-based matching machinery with
concrete predicate + counter + Lean-proved
flip-preservation:

  - **DROPPED UFs**: `MatchingSize`, `IsMatching` (Slice 2.B
    had 4 UFs; Slice 2.C has 2).
  - **KEPT UFs**: `IsMaxMatching`, `ExistsAugPath` (Berge /
    class-restriction live here).
  - **DROPPED axioms**: `mm_size_nonneg`, `mm_size_bounded`,
    `mm_flip_increases` (3 axioms gone — replaced by concrete
    counter + Tier-1 proof).
  - **ADDED local** `c : int` — matching-size counter,
    incremented `c := c + 2` per AP-flip.
  - **Concrete IsMatching**: **4 atoms** per loop's τ
    (range / symm / no_self / edge — see `_MI_*` constants in
    the bench).  The `no_self` atom is NEW vs Slice 2.B and is
    load-bearing (see lesson #73).
  - **τ counts**: τ@L0 → 8 atoms (was 4 in Slice 2.B); τ@L1
    → 10; τ@L2 → 12.

### Synth result + helpers

  - **131.9s wall, 1 verified solution.**  Same algorithm
    shape as Slice 2.B (3-nested AP search + flip + tail-
    recur), but printed `invariant L0/L1/L2:` lines show
    CONCRETE matching predicates instead of `IsMatching G n M
    = 1` UF.
  - **9 Tier-1 PROVEN helpers** in
    `lean/SynthLean/Y2Corpus/l16_max_matching_concrete/Helpers.lean`:
      - **`flip_preserves_im`** — ~120 LOC real Lean proof
        from first principles.  Case-splits `kk ∈ {u, v, M v,
        w}` vs otherwise; pointwise store-unfolding +
        destructuring M's 4 IM atoms.  Replaces Slice 2.B's
        `mm_flip_preserves_matching` AXIOM.
      - **8 Tier-1 helper theorems** (sc1/sc2/sc3/sc5/sc6/
        sc9/sc11/sc14/sc15) — all proven, all match
        translator-emitted signatures.  sc1/sc6/sc14/sc15 are
        FLAT-shape; sc2/sc3/sc9/sc11 are chain-aware (see
        lesson #74).
  - **Axioms kept (user-approved)**: `mm_berge` (Berge's
    classical theorem; multi-day to prove from scratch in
    Lean) and `mm_termination_implies_no_ap` (class-
    restriction).

### Encoding lessons banked

**73. Minimum-correct concrete matching predicate is 4
atoms, not 3.**  Without `no_self` (`M[k] ≠ k` for matched
k), the predicate admits `M[v] = v`, which breaks AP-flip
preservation: the proof's case analysis assumes `{u, v, M
v, w}` are 4 distinct values, which requires `M v ≠ v`.
The 3-atom predicate (range / symm / edge alone) is *more
permissive* but *unsoundly weak* for a flip-preserves-IM
theorem.  When converting a UF (`IsMatching`) to a concrete
predicate, audit which mathematical properties the UF's
axioms implicitly assumed — the `no_self` requirement was
implicit in Slice 2.B's `mm_flip_preserves_matching` axiom
and surfaced only when the proof tried to close.

**74. Helper signature dispatch is FLAT vs chain-aware
depending on chain-prefix structure (extension of lesson
#69).**  For Slice 2.C, sc1/sc6/sc14/sc15 dispatch FLAT
(bare pre-state names + primed post-state for modified
vars); sc2/sc3/sc9/sc11 dispatch chain-aware (`n_s0`/`n_s1`
style binders).  The rule: if the chain prefix to the
constraint's target has only SB items (no Loops), FLAT;
otherwise chain-aware.  Mismatches surface as Lean's
`unknown identifier` errors when the helper cite references
names that aren't in the translator's emitted theorem.

**Mitigation**: smoke-test each helper individually via
`verify_class_via_lean` before committing.  Inspect the
theorem text via `theorem_for_<kind>(...)` if uncertain.

**75. Concrete-predicate τ counts inflate enumeration
cost; minimal-required-atoms helpers (lesson #71) are
essential.**  Slice 2.C's τ@L2 went from 8 atoms (Slice 2.B's
UF) to 12 atoms (4 concrete IM atoms + 8 other), so 2^12 =
4096 subsets per safety-check.  Helpers declare just the IM
atoms they need so per-subset enumeration fires helpers on
partial subsets too.  Without this pattern, sound-mode
rejections on partial subsets would kill the synth.

Concrete-predicate benchmarks should ALWAYS adopt the
minimal-required-atoms pattern — declare the smallest atom
subset that the proof actually destructures, not the full τ
subset.

### Trust-tier comparison: Slice 2.B → Slice 2.C

| Component               | Slice 2.B           | Slice 2.C           |
| ---                     | ---                 | ---                 |
| MatchingSize            | UF + 2 axioms       | concrete counter `c` |
| IsMatching              | UF + axiom          | concrete 4-atom predicate |
| flip-preserves-matching | axiom               | **Tier-1 PROVEN theorem** |
| IsMaxMatching           | UF                  | UF (unchanged)      |
| Berge                   | axiom               | axiom (unchanged)   |
| class-restriction       | axiom               | axiom (unchanged)   |
| **UFs total**           | **4**               | **2**               |
| **Axioms total**        | **6** (incl. matching machinery) | **2** (only Berge + class-restriction) |
| Wall-clock              | 102s                | 131.9s              |

The wall-clock cost (102s → 131.9s, +29%) is dominated by
the larger τ enumeration (12 vs 8 atoms on τ@L2).  The
trust win is the headline: Slice 2.C's solution trusts only
Berge's classical theorem + the class-restriction sufficiency
claim — everything else is concrete arithmetic + Lean-proved
preservation.

### Research direction unlocked

**Axiom-tightening of synthesized algorithms via Lean-
proved transition-preservation theorems is tractable.**  The
pattern: take a benchmark that relies on UF + axiom
abstractions; identify the load-bearing axiom (here:
`flip_preserves_matching`); rewrite it as a Tier-1 Lean
theorem about the concrete data; rebuild the surrounding
helpers to destructure the concrete predicate.  Each axiom
displaced is a concrete trust-reduction win.  The Slice 2.B
→ 2.C move went from 5 trusted axioms to 2; the residual
axioms (Berge, class-restriction) are genuine "classical
mathematics" claims, not algorithm-step preservation.

This generalizes to any axiom-heavy benchmark: the
flip-preserves-IM pattern (case-split on the modified set,
destructure the concrete predicate's atoms, dispatch via
omega + direct hypothesis citations) should port to other
"local-mutation preserves invariant" lemmas.

---

**Phase Slice 2.B — max matching with axiomatized Berge
(2026-05-25).** 🎯 **MILESTONE — first end-to-end recursive
maximum-matching benchmark; framework's first 4-loop / 4-UF /
6-axiom synthesis.**

`benchmarks/open_prbs/l16_bipartite_matching/bench_max_matching_recur.py`
synthesizes 1 verified solution in **102s wall**.  The
algorithm: 3-nested AP search (u, v, w loops) + flip on
found-flag + tail-recur `M := synth(G, n, M, k - 1)` with
`phi@PROC = k`.  8 Tier-3 helpers in
`lean/SynthLean/Y2Corpus/l16_max_matching_recur/Helpers.lean`
(sc2/sc3/sc5/sc6/sc9/sc11/sc14/sc15).  See
`benchmarks/open_prbs/l16_bipartite_matching/SLICE_2B_STATUS.md`
for the complete narrative.

### Algorithmic story

`IsMaxMatching` and Berge's theorem are axiomatized as UFs +
axioms (4 UFs: `MatchingSize`, `IsMatching`, `IsMaxMatching`,
`ExistsAugPath`; 6 axioms covering matching theory + Berge +
class-restriction).  The synth picks the canonical tail-
recursive shape:

```
M := synth(G, n, M, k - 1)        // recur with budget k-1
if found:  M := flip-augpath(M, u, v, w)
return M
```

The iteration budget `k` is the framework workaround for
identity-args tail recursion: the natural design
(`args.M = M-updated-by-loop`) makes `phi(in_b) > phi(args)`
shape into `x > x` (always false) because the framework
doesn't track procedure-entry-state separately from in_b's
state.  Adding an explicit `k: int` input bounded by `n / 2`
and `phi@PROC = k` makes decrease trivial (`k > k - 1`).
Option (b) — a framework refactor to track procedure-entry-
state distinctly — is the principled fix; deferred.

### Three framework + solver fixes that closed Slice 2.B

#### 1. `chain_paths_local` atom_refs preservation (commit d69ce41)

`synth/constraints.py:chain_paths_local` is a generator over
Cartesian paths through a chain of multi-branch SBs.  Each
path calls `tau_at(...)` during `per_item` construction,
appending τ atom_refs to a shared `current_refs` accumulator.
The FIRST commit captured `current_refs` AND cleared it
(line 285); subsequent Cartesian paths committed with an
empty `current_refs` — recorded with `atom_refs=[]`.

**Effect on sc14 of max-matching specifically**: sc13 (first
Cartesian path through final SB(n=2)) had `atom_refs` with 4
τ@L0 refs; `_extract_loop_id` returned `"L0"`; helper
short-circuit gated correctly.  sc14 (second Cartesian path)
had empty `atom_refs`; `_extract_loop_id` fell back to
atom_refs, got nothing, returned None; helper short-circuit
silently SKIPPED.  sc14 then wedged on generic Lean.

**Fix**: snapshot the refs accumulated during per_item build
and restore them per yielded iteration.  Each Cartesian
path's commit captures the same refs.  Trivial patch in
`chain_paths_local` (~lines 360-415 of constraints.py).

**Result with fix**: helper short-circuit fires on every
Cartesian path through the SB; sc14 closes via the helper.
Reduces v11's wall-clock from a wedge to 117.7s.

This is a soundness-adjacent fix.  Before the fix, second-
Cartesian-path constraints had no `loop_id` binding, so
cubes might have been emitted with insufficient τ gating.
(In practice the gating was inferred correctly enough that
no unsound code shipped, but the invariant was broken.)

#### 2. Chain-bundle `init_extras` (commit b339a61)

Pre-loop SBs writing non-loop-modified vars (e.g., the
`saved := A[0]` save-and-restore pattern in
array_rotate_left) now emit `h_init_<var>` hypotheses in
chain-aware bundle theorems, mirroring the existing
`h_skip_<var>` for post-loop writes.

This was a partial framework gap — the dual case (post-loop
SB writes a loop-modified var) is still NotImplementedError
because the abstract Loop transition doesn't track per-
iteration value history.  Out of scope for Slice 2.B; not
blocking any current benchmark.

#### 3. Slice 2.B closure — solver coverage routing + minimal-helper pattern (commit 01f9cb0)

**Solver routing**: `synth/solver.py`'s axiom-heavy Lean
dispatch gate was filtering on `_extract_loop_id(sc) is not
None`, which excludes **procedure-level coverage** (`coverage`
kind with `loop_id=None`).  The translator
(`theorem_for_coverage`) already handles this case via
`_find_top_level_multibranch_sb`.  Two-line carve-out: route
`coverage` with `loop_id=None` to Lean when the benchmark
has axioms.

**Minimal-helper pattern**: `mm_sc15_coverage` requires ONLY
τ@L0 atom 2 (`found ∈ {0,1}`), not the full subset.  Proof
body is `exact h_tau_2.symm` (the RHS `g@B4.0 ∨ g@B4.1 =
(found==1) ∨ (found==0)` derives from atom 2 alone).

Why this matters: per-subset enumeration tries 2^|τ@L0|
partial subsets.  If the helper requires the FULL τ subset,
only the full-subset cube fires via short-circuit; partial
subsets fall through to generic Lean (often UNKNOWN → sound-
mode rejection).  Restricting `required_atoms` to the
genuinely-needed subset enables the helper to fire on EVERY
τ subset containing that atom — eliminating the 8 partial-
subset UNKNOWNs that caused Slice 2.B's UNSAT before the
pattern was applied.

### Encoding lessons banked

**70. `chain_paths_local` generator-vs-mutation atom_refs
bug.**  When a generator function uses a shared mutable
accumulator that gets captured-and-cleared on each yield,
only the first yielded iteration captures the accumulator's
state; subsequent yields see an empty accumulator.  In our
case, the per_item-construction-time `tau_at(...)` calls
appended to `current_refs`; the first commit cleared it;
subsequent commits recorded empty `atom_refs`.

Symptom: helper short-circuit silently skips a constraint
because `_extract_loop_id(sc)` falls back to atom_refs and
returns None.  Detection: compare atom_refs counts across
constraints of the same kind/loop_id.  If sc<N> has 4 refs
and sc<N+1> (same kind, presumably same chain context) has
0, suspect the generator-vs-mutation pattern.  The fix is
to snapshot the accumulator at generator entry and re-apply
per yield.

This generalizes: any time a generator yields a "captured
state" and the captured state lives in a shared mutable
container, you must either (a) snapshot before yielding and
restore on next iteration, or (b) deep-copy at the yield
boundary.  Python's generator semantics give you the
flexibility but not the safety.

**71. Minimal-required-atoms helper pattern.**  When a
helper's proof needs only 1-2 τ atoms (not the full τ
subset), declare `required_atoms` to be just that minimal
subset.  Per-subset enumeration then fires the helper on
every τ subset containing those atoms (subset semantics:
the cite type-checks because the helper's hypotheses are a
SUBSET of the available `h_tau_<i>` binders at the larger
cube).

If `required_atoms` lists the FULL τ subset, the helper
short-circuit only fires once (on the full-τ cube); partial
subsets fall through to generic Lean, often timing out into
UNKNOWN → sound-mode rejection → global SAT UNSAT.

Example: `mm_sc15_coverage` requires only τ@L0 atom 2 (the
`found ∈ {0,1}` atom).  The coverage RHS `g@B4.0 ∨ g@B4.1 =
(found==1) ∨ (found==0)` derives from atom 2 alone via
`exact h_tau_2.symm`.  Declaring `required_atoms =
{"tau@L0": frozenset({2})}` lets the helper fire on all
2^(|τ@L0|-1) subsets containing atom 2 — eliminating 8
sound-mode rejections at once.

General rule: write the proof to use the fewest atoms
possible (helpers should be "what does THIS conclusion
need?"); the `required_atoms` declaration should reflect
that minimum.

**72. Procedure-level coverage needs explicit kind gate in
the axiom-heavy Lean dispatch.**  Multi-branch SB(n>1) at
the procedure top level (NOT inside a Loop) emits a
`coverage` constraint with `loop_id=None`.  The standard
solver gate `_extract_loop_id(sc) is not None` filters this
out, but the translator (`theorem_for_coverage`) handles it
via `_find_top_level_multibranch_sb`.

Two-line carve-out in solver.py: explicitly route
`coverage` constraints with `loop_id=None` to Lean dispatch
when the benchmark has axioms.  Without this, axiom-heavy
benchmarks with procedure-level branching wedge on Z3's
quantifier-instantiation heuristics.

This is the generalization of the K.A-era fix that handled
Loop-level coverage; procedure-level was the dual gap.
Worth noting in problem.skill's atom-shape reference and in
debug.skill's triage table.

---

## Older phases — see CHANGELOG.md

Every phase older than the most recent ~3 lives in
[`CHANGELOG.md`](./CHANGELOG.md).  When citing historical
phases (e.g., for lessons-banked tracebacks or
implementation context), point by phase name.

## Process docs — moved

**Phase-completion routine** and **Experience-report rule**
both moved to [`CONTRIBUTING.md`](./CONTRIBUTING.md)
(2026-06-07).  Subagent prompt template, file-by-file sync
table, and case-study criteria all live there.

## Always-on reminders

**Moved to [`PRINCIPLES.md`](./PRINCIPLES.md) (2026-06-07).**
The full text — governing principles (P-1 framework over
single-case, P-2 axiom-free preferred, P-3 dummy `0==0`
axiom for quantified-array benchmarks, P-4 Lean-axiomatize
+ Z3 shim), implementer reminders (A-1 scratch-first Lean,
A-2 Tier-2-first authoring, A-3 <10s runtime budget, A-4
transcript rotation), and project conventions — lives in
`PRINCIPLES.md`.

Quick reference (the principles by name):
- **P-1**: framework improvements over single-case fixes.
- **P-2**: axiom-free preferred — Tier-1 over Tier-2.
- **P-3**: dummy `["0 == 0"]` axiom for quantified-array
  benchmarks.
- **P-4**: Lean axiomatize + Z3 shim, not pure Z3 SAT past
  the wedge limit.
- **A-1**: iterate non-trivial Lean proofs in scratch first.
- **A-2**: Tier-2-first authoring workflow for new helpers.
- **A-3**: target <10s wall-clock per benchmark.
- **A-4**: session-transcript rotation cadence.

