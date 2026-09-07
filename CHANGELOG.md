# CHANGELOG.md

Phase-by-phase history of the synthesizer project.  Most
recent phases (last ~3) stay in `CLAUDE.md` for active-
session context; everything older lives here.

Each entry follows the shape:
- **Phase name** (date marker, milestone status emoji).
- One-paragraph headline of what shipped.
- Details (constraint kinds, benchmarks, lessons banked,
  trust-surface changes).
- Encoding lessons banked (numbered, project-wide).

Originally inline in `CLAUDE.md §Current phase`; split here
on 2026-06-07 as part of the doc reconcile.

When citing a historical phase from active docs, point by
phase name (e.g., "CHANGELOG §Phase K.D.W").

---

**Phase K.D.W — per-constraint wedge detection + K.3.2 full
3-nested synth (2026-05-25).** 🎯 **MILESTONE — diagnostic
infrastructure for "needs-helpers" verdicts + first concrete
3-nested-loop augmenting-path search.**

Two pieces landed:

### Per-constraint wedge detector (commit `2cde52f`)

`Problem.wedge_threshold: int | None = 30` (new field on
`synth/ir.py`).  The solver tracks per-constraint Lean
dispatch outcomes (non-valid only); two thresholds:

  - **WARN at `wedge_threshold`**: one-time message
    `[WEDGE] sc<N> (kind=..., loop_id=..., branch_idx=...):
     K non-valid Lean dispatches; consider authoring a Tier-3
     helper ; inspect ls dump_dir/sc<N>_*.failed.lean`.
  - **ABANDON at `2 × wedge_threshold`**: stop enumerating
    that constraint.  Subsequent dispatches defer
    immediately; the ThreadPoolExecutor's queued futures are
    cancelled via `shutdown(wait=False, cancel_futures=True)`.
    In-flight futures (≤ worker count) drain naturally.

End-of-run: when any constraints abandoned, return
`NoSolution(reason="needs-helpers")` with hints listing each
wedged constraint + its `(kind, loop_id, branch_idx)` tuple
+ a sample failure-dump path.

**Default threshold rationale**: 30 is high enough that
legitimate axiom-heavy benchmarks (fib, which distributes
its ~hundreds of dispatches across many constraints — ~tens
per) don't false-flag, but low enough to surface true
wedges in minutes rather than hours.

**Soundness**: abandoned constraints contribute empty-or-
partial valid-cubes lists; the main SAT will UNSAT them; the
synth returns `NoSolution` (sound rejection), never an
unverified solution.  See SOUNDNESS.md.

**Validation on `bench_aug3_two_loops` with `helper_registry=None`
+ `wedge_threshold=10`**: all 4 wedge-prone constraints surface
and produce a clean `needs-helpers` verdict in 830s, instead of
a silent multi-hour wedge.

### K.3.2 full 3-nested-loop AP search (commit `1f5a34f`)

`benchmarks/open_prbs/l16_bipartite_matching/bench_aug3_three_loops.py`
— 1466s, 1 verified solution.  First concrete (non-
axiomatized) 3-nested-loop augmenting-path search to
synthesize via the framework (u, v, w all iterated).

6 Tier-3 helpers in
`lean/SynthLean/Y2Corpus/l16_aug3_three_loops/Helpers.lean`:

  - `k32_3l_middle_entry`  (sc1, L1 entry-bundle after B1)
  - `k32_3l_inner_entry`   (sc2, L2 entry-bundle after B2)
  - `k32_3l_inner_break`   (sc4, L2 inner break with
    τ_L1 consequent)
  - `k32_3l_middle_body_ind` (sc8, L1 body inductive via L2
    abstract)
  - `k32_3l_outer_body_ind`  (sc10, L0 body inductive via L1
    abstract)
  - `k32_3l_final`         (sc12, L0 final bundle ⇒ post —
    FLAT-shape signature, not chain-aware; see lesson #69)

The wedge detector caught a missing sc1 helper on the first
run (60 dispatches before abandonment; the `NEEDS-HELPERS`
hint pointed straight at it); the second run with the added
helper closed in 1466s.

### Encoding lessons banked

**68. Per-constraint wedge detection is a free diagnostic
for "I need a Tier-3 helper here".**  Without it, a wedge
looks like a silent multi-hour run; with it, the wedging
constraint surfaces inside minutes with a clean
`needs-helpers` verdict and a pointer to the failure-dump
path.  Cost: ~120 LOC across `solver.py` + `ir.py`.
Benefit: every future benchmark gets a clean fast-fail when
a constraint needs help.  Soundness is preserved (abandoned
constraints contribute no valid cubes; the main SAT
UNSATs the obligation cleanly).

**69. `verify.py` dispatches L0-level chain-bundle-post to
the FLAT translator, not chain-aware, when L0's chain
prefix has no non-SB items.**  Helper signatures must match
the actual translator output.  For K.3.2 3-nested's `sc12`
(L0 final bundle ⇒ post), the chain prefix was a single
SB(init) — verify.py routed to `theorem_for_chain_bundle`
(FLAT — pre-loop vars unprimed, post-loop primed), NOT
`theorem_for_chain_bundle_chain`.  Helper `k32_3l_final`
was authored with chain-aware `_sN` binders first; the cite
failed type-checking until the helper signature was
reshaped to the FLAT (pre/post) form.

The general rule: emit the theorem with the translator and
match binder names exactly, especially at L0 level where
the dispatch can flip between FLAT and chain-aware
depending on chain-prefix structure.  Worth noting in
problem.skill's helper-authoring section.

---

**Phase K.D — chain-aware break + 2-loop K.3.2 AP search
(2026-05-25).** 🎯 **MILESTONE — nested-loop break primitive
validated end-to-end on real graph algorithm.**

Branch `c1d/chain-aware-break`.  Three commits land here:

  - `b347fdd` — K.D.IMPL-1/5: chain-aware break for nested
    Loops.  When the breaking Loop is nested inside an
    enclosing Loop, the break-bundle obligation's consequent
    is `τ_enclosing(body_out)` instead of `Fpost(body_out)`.
    The inner break exits to the enclosing loop's body, which
    still must satisfy its own invariant.

    Also: enclosing Loops containing a break-capable inner
    Loop need the inner Loop's abstract transition relaxed
    — the inner exit can have `g_inner` still true (early
    exit via break), so we drop `¬g` from the abstract Loop
    transition when the body has direct break branches.
    `_has_break_branch` is non-recursive on Loop: an inner
    Loop's break exits the inner Loop, not the enclosing one.

  - `1f0d31f` — research §K.D.8 status doc.

  - `ae95e8d` — K.D.IMPL-6: K.3.2 2-loop AP search.  The
    first L1.6 benchmark to perform CONCRETE 2-nested-loop
    augmenting-path search using nested loops + `break` +
    the `found`-flag idiom for outer-loop short-circuiting.

### Synthesized algorithm (`bench_aug3_two_loops.py`)

```
v, w, found := -1, 0, 0
while (v + 1 < n and found == 0):
    v, w := v + 1, 0
    while (w < n):
        if (v != u and G[u][v] >= 1 and M[v] != -1 and
            w != u and w != v and w != M[v] and
            M[w] == -1 and G[M[v]][w] >= 1):
            found := 1
            break
        else:
            w := w + 1
return M, found
```

**578s wall, 1 verified solution, 3 Tier-3 helpers** —
`k32_2l_inner_entry` (sc1), `k32_2l_inner_break` (sc3),
`k32_2l_outer_body_inductive` (sc7).  Each helper closes
via omega + direct hypothesis citations since the algorithm
doesn't modify M; MI is carried trivially through frame eqs.

### Framework improvements (also banked on this branch)

**1. Fpre is now propagated into recursive `walk_template`
calls.**  Pre-condition facts about input vars are
immutable across loop iterations (inputs never change),
so Fpre evaluated at any state where input vars are bound
is equal to Fpre at the initial state.  Including Fpre in
the recursive walk's `pre_fn` lets inner constraints rely
on input facts without forcing the user to carry them in
outer τ.  Trims |τ_outer| from 7 atoms to 3 atoms in
bench_aug3_two_loops.

**2. The chain-aware Lean translator's
`_emit_chain_item_hyps` now drops `¬g` from break-capable
Loops' abstract transition** — parallel to the Z3-side
K.D fix in `constraints.py`.  This was a SOUNDNESS BUG:
Lean had a STRONGER hypothesis set than Z3, so Lean could
over-validate (prove obligations Z3's actual obligation
couldn't).  Now they match.  See lesson #66.

### Smoke benchmark

`bench_nested_break_smoke.py`: outer Loop containing inner
Loop with break; inner break sets nothing but propagates
τ_outer through frame eqs.  Synthesizes in 0.3s.  Pure
framework smoke (no graph algorithm content).

### Encoding lessons banked

**66. Lean and Z3 verifier obligations must be SEMANTICALLY
EQUIVALENT, not just "similarly shaped".**  The chain-aware
Lean translator emitted `¬g` for every Loop in the chain,
including break-capable Loops.  Z3's `constraints.py` (after
K.D) drops `¬g` for break-capable Loops.  So Lean was being
asked to prove a STRONGER statement than Z3 — Lean had more
hypotheses, so it could close obligations Z3 couldn't.

The verify oracle treats Lean VALID as a class-valid signal.
If Lean validates with a hypothesis set Z3 doesn't have, the
synth includes the class in cubes, and the final solution
relies on Z3's actual obligation being valid — which it
might not be.  Unsound.

The fix is mechanical: every time you change which
hypotheses the Z3 constraint includes (or excludes) for a
construct, you have to make the parallel change in the
Lean translator.  Mismatch = unsoundness, even when each
side individually looks correct.

**67. Find-flag + outer-guard `found == 0` is the standard
encoding for early-exit across nested loops.**  The `break`
primitive only exits the innermost loop.  To short-circuit
remaining outer iterations, the inner-break branch sets a
`found` flag, and each outer loop's guard includes
`found == 0`.  After the inner break sets `found := 1`,
the outer guard re-checks on next iter and exits naturally.

The "increment-at-start" pattern keeps inner Loops as the
LAST item in their enclosing body chain (so the break's
consequent `τ_enclosing(body_out)` doesn't need chain-tail
composition).  Initialize counters to `-1`, increment in
the enclosing body's prep SB, and the inner Loop's exit
state IS the enclosing body's terminating state.

This unlocks all K-style "search nested + exit on hit"
algorithms (Hopcroft-Karp's BFS+DFS layers, etc.) within
the existing framework — no new IR primitive needed beyond
the `_break` flag.

### Deferred

  - **K.D.2.a** (chain-tail after break): break in a Loop
    that's NOT the last item in its enclosing body's chain.
    Needs chain-tail composition between body_out and
    τ_enclosing.  Workaround: restructure the algorithm so
    inner Loop is last (the increment-at-start pattern).
    Not blocking any current benchmark.

  - **K.3.2 full 3-nested** (u, v, w all iterated).
    **DONE — see Phase K.D.W entry above** (commit `1f5a34f`,
    `bench_aug3_three_loops.py`, 1466s, 6 Tier-3 helpers).
    Framework's K.D pieces all worked for this; cost was
    purely benchmark-level (τ design + 6 helpers).  The
    wedge detector (Phase K.D.W) caught a missing helper
    cleanly on the first run.

---

**Phase L1.6 Slice C — multi-template parallel exploration
(2026-05-23).** 🎯 **MILESTONE — algorithm-shape exploration
validated; the algorithm-exploration tripod closes.**

`bench_l16_multi_template.py` (commit `98e4b76`) + the parallel-
subprocess harness `synth/multi_template.py` (foundation
`1861ded`).  First multi-VARIANT exploration at the TEMPLATE
level — three algorithm shapes for the same matching spec on
a clique-graph precondition:

  - **T_A linear sweep**: PICK, 316s, score 29.50.
    `i=0; while i<n-1: pair (i,i+1); i+=2; c+=2`.
  - **T_B two-pointer**: PICK, 652s, score 37.50.
    `left=0; right=n-1; while left<right: pair (left,right);
    left+=1; right-=1; c+=2`.
  - **T_C no-op**: REJECT, 0s.  `c := 0`, no loop.
    Framework correctly rejects at safety-bundle-post (count
    post `c >= n - 1` fails for n > 1).

Sequential dispatch (`max_workers=1`) — 969s total wall.
Parallel mode revealed Lean cache contention under concurrent
synth subprocesses; the sequential workaround keeps subprocess
isolation while eliminating CPU/disk contention.  Documented
as Slice C's parallel-contention finding (RESEARCH.md §I,
lesson #61).

**Architecture decision** (RESEARCH.md §I; EXPERIENCE_REPORT.md
CS-13): multi-template explored via parallel-subprocess
harness, NOT unified-SAT with a `TemplateUnion` IR node.  The
user pushed back on the "obvious middle-of-the-road"
recommendation; the pushback was load-bearing — Architecture B
preserves every Slice C goal on a substantially simpler
implementation (~150 LOC harness + zero IR changes).

**4 Tier-3 helpers across T_A and T_B**.  T_C needs none
(correctly rejected).  T_B's spec needed iteration: phi
changed from `right - left` to `right - left + 1` and a new
τ atom `left <= right + 1` added (load-bearing for ranking-lb
at the loop-exit state).  See `benchmarks/open_prbs/l16_bipartite_matching/REPORT.md`
for very detailed exploration narrative including the
iteration story.

### Encoding lessons banked from Slice C

61. **Multi-template should NOT be unified-SAT.** The
    intuition "let the SAT solver search jointly over
    algorithm shapes" is wrong for our IR.  Templates don't
    share indicator bits; per-class enumeration stays N×;
    parallelism is the dominant speedup dimension.  When
    multi-shape exploration becomes desirable, the right
    architecture is an orchestration layer that runs N
    independent `solve()` calls in parallel — never a single
    SAT covering the union.  Recorded in RESEARCH.md §I.

62. **Parallel multi-template hits Lean cache contention on
    expensive variants.**  3 synth subprocesses × ~4 internal
    Lean workers saturate an 8-core host; `.solved.lean`
    cache lookups via `lake env lean` time out at 15s under
    load → spurious unknown verdicts.  Workaround: run with
    `max_workers=1` (sequential dispatch via the same
    harness).  Smoke benchmarks parallel cleanly; expensive-
    per-variant benchmarks need serial.  Same harness, one
    knob change.

63. **Loop-exit ranking-lb is a real spec trap for two-pointer
    shapes.**  T_B's initial phi `right - left` is negative at
    exit (where `¬(left < right)` means `left ≥ right`).
    Manual inspection of the spec doesn't surface this —
    the loop GUARD makes the expression always positive
    while looping.  The framework's per-class enumeration
    catches it: hint `"ranking-lb has no valid attribute
    class — predicate space lacks the atoms needed."`  Fix:
    add τ atom `left ≤ right + 1` and bump phi to `right -
    left + 1`.  Pattern generalizes: any phi that goes to
    zero at the loop-exit boundary needs a `+1` shift OR an
    explicit τ atom that captures the boundary case.

---

**Phase L1.6 Slice B — concrete matching operations + Slice A → B
unification (2026-05-23).** 🎯 **MILESTONE — concrete-ops
multi-candidate exploration validated.**

Four sub-slices that progressively replace Slice A's UF
axiomatization with concrete IR operations on `int[][]`
adjacency + `int[]` matching state.  Commit refs in parens.

### B.1 (`815f241`) — first concrete matching synth E2E

`benchmarks/open_prbs/l16_bipartite_matching/bench_pair_consecutive.py`.
Template `SB() >> Loop(SB(n=2))`.  Body pairs `(i, i+1)` if
`G[i][i+1] >= 1`, advances by 2 otherwise.  Quantified
matching-invariant is over `M[k]` / `G[k][M[k]]` reads —
NO UFs.

  - 1 solution in 695s.  τ minimized to
    `{0 ≤ i, i ≤ n, matching-invariant}` — unmatched-tail
    redundant under conjunctive enumeration.
  - Load-bearing helper `sc2_fallthrough_cb44bbf0.solved.lean`
    (~50 LOC): case-split on `k ∈ {i, i+1, else}` for MI
    preservation, cites `h_pre_sym` for the `G[i+1][i] = G[i][i+1]`
    symmetric-graph fact.
  - Trimmed τ from 5 atoms (initial design) to 4 atoms — the
    `n ≥ 0` atom was load-bearing for nothing the pre couldn't
    carry; trimming shrinks the 2^|τ| enumeration 2×.

### B.2 (`f089eee`) — multi-candidate at concrete level

`bench_pair_multi_count.py`.  Same template; 3-candidate
pool at `s@B1`:
  - Cand 0 (full-pair): `M[i]:=i+1, M[i+1]:=i, c+=2`.
  - Cand 1 (asymmetric): `M[i]:=i+1`, `c+=1`.
  - Cand 2 (skip): no `M` update, `c+=0`.

Discrimination mechanism: a counter program variable `c: int`
and the invariant `c >= i`.  Each iteration advances `i` by 2;
only Cand 0 keeps `c` in lockstep.  Cand 1 and Cand 2 can't
preserve `c >= i`, so the inductive obligation fails for them.

  - 1 solution in 405s.  Cand 0 PICKED, Cands 1 & 2 rejected.
  - Concrete-operations analog of Slice A's UF-based
    exploration — same picking mechanism, no UFs.
  - Helper `sc1_fallthrough_f16e259e.solved.lean` ports
    cb44bbf0 with the new `c >= i` atom and `c' = c + 2`
    transition.

### B.3 (`ca7c700`, `74cd3d5`, `269af14`) — source emitters for int[][]

  - **emit_py**: `int[][]` → `list[list[int]]`; 4-arg
    `Update(A, i, j, v)` → `A[i][j] = v`.  Quantified atoms
    become `all(...)` / `any(...)` comprehensions over
    `range(0, n)` filtered by the antecedent.  Two modes:
    default (proof as comments) and `runtime_check=True`
    (proof obligations lowered to `synth.proof_runtime`).
  - **emit_c**: `int[][]` → `int **` (row-pointer array).
    4-arg Update extends the existing temp-capture pattern.
  - **emit_rust**: input-only `int[][]` → `&[&[i64]]`;
    in-place / output → `&mut [Vec<i64>]`.  Chained subscripts
    `G[(i) as usize][(j) as usize]` work via the existing
    AST-based `_cast_subscripts` rewriter.
  - Tests: `tests/test_emit_c.py:test_matrix_init` +
    `tests/test_emit_rust.py:test_matrix_init` round-trip the
    2D-Update path end-to-end (synth → emit → compile → run).
    Both suites: 12/12 pass.  `scratch/pair_consec_emit_demo.py`
    and `scratch/matrix_init_emit_demo.py` are reusable demos.

### B.4 (`10f3345`) — Slice A → Slice B unification

`bench_glover_concrete.py`.  Same 3-candidate pool as B.2
plus `cost_target = "n"` and `cost@L0 = "n - i"`.  **First
benchmark to validate the cost-bound infrastructure
(COST_INVS §§1–4) on concrete-operations templates.**

  - 1 solution in 441s.  Same Cand 0 PICKED outcome.
  - The 3 cost obligations (cost-lb, cost-decrement,
    cost-budget) all close via Z3-LIA — no NIA tax.
  - Helper `sc2_fallthrough_fb5e83c0.solved.lean` ported
    from B.2's `f16e259e` via a one-line sed rename
    (`sc1_fallthrough → sc2_fallthrough`) — the only
    signature delta was the constraint INDEX (cost
    obligations sort before safety, shifting sc1 → sc2).
    Same case-split + omega proof.

**Unification claim**: multi-candidate exploration + cost-bound
discrimination works WITHOUT UF crutches.  Slice A's
algorithm-picking mechanism transfers cleanly to concrete
operations.  COST_INVS §5 records the §§1–4 validation on
concrete state.

### Encoding lessons banked from Slice B

57. **The matching-invariant `M[k] != -1 → 0 ≤ M[k] < n ∧
    G[k][M[k]] >= 1` is the natural concrete-ops analog of
    Slice A's `is_valid_pm(G, n, i, M) == 1` UF.**  No symmetry
    constraint (`M[M[k]] = k`) — left out because chain graphs
    don't need it AND because the asymmetric candidate in B.2
    pre-validates the post but fails the count invariant (which
    is what discriminates).  When porting an axiomatized
    predicate to concrete, ask "what's the minimum atom set
    that preserves under the picked transition?" rather than
    porting every UF axiom.

58. **Counter program variables are the cleanest concrete-ops
    discriminator.**  Slice A's UFs encoded "this step
    preserves the matching invariant" via per-candidate
    axioms.  Concrete equivalent: a counter `c: int` that the
    candidates increment by DIFFERENT amounts, gated by the
    invariant `c >= i`.  Only the candidate stepping `c` in
    lockstep with `i` preserves it.  This works without any
    quantified-array reasoning — pure linear arithmetic
    discrimination, Z3-LIA throughout.

59. **Tier-3 helpers port across related benchmarks via the
    signature-hash mechanism + a sed rename.**  B.2's helper
    (`f16e259e`) extended B.1's (`cb44bbf0`) with new state
    binders (`c`, `c'`).  B.4's helper (`fb5e83c0`) is
    literally `sed 's/sc1_fallthrough/sc2_fallthrough/g' B.2`
    — the only delta was the constraint INDEX because cost
    obligations sort before safety.  Implication: when
    designing follow-up benchmarks that share a proof skeleton,
    the per-benchmark Tier-3 cost is one rename + a recompile,
    not new proof engineering.

60. **Trim τ before the first synth run.**  bench_pair_multi_count
    initially had 5 τ atoms; running with axiom-heavy routing
    disables Phase 3.L's monotonicity fast-path, so the 2^|τ|
    enumeration cost is real.  Dropping `n ≥ 0` (h_pre carries
    it) halved the enumeration.  Each non-load-bearing τ atom
    costs a 2× factor on axiom-heavy benchmarks — be more
    aggressive about pruning than on Z3-only benchmarks.

---

**Phase COST_INVS — resource-bound invariants landed + L1.6 (1)
first end-to-end cost-bound matching benchmark (2026-05-22).** 🎯
**MILESTONE — north star #1 substrate.**

A multi-slice landing that pulls north star #1 ("from correctness
to full resource semantics") from design into working code, plus
the first cost-bound graph-flavored benchmark.  Full design doc
in `COST_INVS.md`.  Commit refs in parens.

### §1 + §1.5 — IR extension

- **`Problem.cost_target: str | None = None`** (`7ee9212`).
  When set, `expand` allocates a `cost@<lid>` hole per Loop
  alongside the existing `phi@<lid>`; user supplies candidate
  cost expressions via `atoms[f"cost@{lid}"]`.  Three new
  soundness-critical constraint kinds emitted in
  `constraints.py`:
    - `cost-lb`: `Pre ∧ τ ⇒ cost@L(state) ≥ 0`.
    - `cost-decrement`: `cost(body) ≤ cost@L(in) - cost@L(out)`
      (body_cost = 1 for SB-bodied loops; sum-over-items for
      non-SB bodies — see §1.5).
    - `cost-budget`: top-level `Pre ⇒ cost@L0(pre_state) ≤
      cost_target(input)`.
  All three added to `_REJECT_UNKNOWN_KINDS` in `solver.py` —
  cost obligations are soundness-critical, not opt-in.  Decoder
  prints `cost      L<lid>: <expr>` parallel to `ranking`.

- **§1.5 nested-loop cost composition** (`6998deb`).
  `walk_template` gains an `enclosing_loop_id` parameter; when
  set, after the per-construct step it emits a cost-decrement
  constraint per Cartesian path through the body chain, summing
  per-item body costs:  SB→1, Loop(inner)→cost@L_inner(entry),
  Recur→0 (deferred to §1.6).  First nested benchmark
  `benchmarks/cost_invs/nested_cost.py` synthesizes the
  doubly-nested counter with `cost_target = "n * (n + 2)"`,
  picking `cost@L0 = (n - i) * (n + 2)`, `cost@L1 = n - j`.

### §2 — Lean cost-composition lemma library + wiring

- **§2 lemma library** (`c214153`): `lean/SynthLean/CostLemmas.lean`
  with 11 named polynomial identities covering linear cost
  identities, quadratic decrement step, nested-loop composition,
  cost-budget closed forms.  All discharged via `ring`/`omega`/
  `nlinarith`; compiles in 5.4s under `lake build`.  Imported
  from `SynthLean.lean` root.

- **§2 wiring** (`0a11475`): three Lean translators in
  `synth/lean_backend/translate.py` —
  `theorem_for_cost_lb`, `theorem_for_cost_decrement`
  (SB-bodied), `theorem_for_cost_decrement_chain` (non-SB-bodied;
  reuses `_chain_state_binders` + `_emit_chain_item_hyps`).
  `verify.py` dispatches to the chain variant when the outer
  Loop body is non-SB.  `cost-lb` and `cost-decrement` added
  to `_LEAN_TRANSLATABLE_KINDS` so `_on_unknown` routes them
  through Lean.  Tactic chain:
  `omega | ring_nf+omega | nlinarith | linarith`, with
  `open SynthLean.CostLemmas` available for citation.

- **§2 import-bug fix** (`2506cdd`): the cost-* Lean dispatch
  was emitting `open SynthLean.CostLemmas` WITHOUT the
  corresponding `import SynthLean.CostLemmas` at file head,
  so `lake env lean` returned silent UNKNOWN (the namespace
  resolution failed but the tactic chain swallowed it).
  One-line translator fix.  After: cost-* validation actually
  uses the lemma library.

**Speedup NOT delivered on `bubble_sort_cost`.**  Z3 returns
VALID (slowly, via NIA) rather than UNKNOWN, so Lean
fallthrough doesn't fire on the quadratic cost-decrement.  An
aggressive "always-route nested cost-decrement to Lean" gate
was tried and reverted — per-subset Lean startup × N subsets
exceeded Z3's NIA total.  bubble_sort_cost stays at ~28s.
Deferred follow-up: quadratic-routing heuristic (gate
Lean-first on nonlinearity signal in the cost atom).

### §3 — Graph + bipartite-matching Lean substrate

- **§3 substrate** (`d7e7f35`).  Two new modules:
  - `lean/SynthLean/Graph.lean`: Adj, Undirected, Simple,
    Bipartite, IntervalGraph, BoundedEndpoints predicates;
    EdgeCount and Degree UFs with non-neg axioms.
  - `lean/SynthLean/Matching.lean`: IsMatching,
    IsMaxMatching predicates; MatchingSize UF with non-neg +
    |M| ≤ N/2 bounds; Konig theorem (axiomatized); named-
    algorithm cost axioms `HopcroftKarpCost`,
    `GloverIntervalCost`, `BucketedIntervalCost`;
    `ExistsMaxMatching`; IntSqrt / IntLog2 Int-typed
    placeholders.

  Both compile under full `lake build` (3-7s each).  Pattern
  follows L1.2/L1.5: verified sub-algorithms + structural
  facts declared as Lean AXIOMS (trusted), compositions
  searched with Z3 + cost-decrement on top.

### §4 — L1.6 template speculation framework

- **§4** (`aeb9d35`).
  `benchmarks/open_prbs/l16_bipartite_matching/speculate.py`
  enumerates (template, cost-target) pairs, emits Lean
  theorems citing §3 cost axioms, dispatches via
  `lake env lean`, tabulates verdicts.

  First sweep (T1 Glover / T2 Bucketed / T4 Hopcroft-Karp
  × {LOOSE, LINEAR, TIGHT_OPEN}):
    - 2 self-matching valid pairs (each template achieves
      its own bound).
    - 6 cross-pair invalids.
    - **TGT_TIGHT (N + E - 1) INVALID for ALL templates.**

  Framework-checked structural impossibility narrative for
  L1.6's open question — same L1.2-pattern shape but at the
  cost-bound level.  Lean closes each pair in ~4.5s.

- **Lower-bound axioms** (`0054b3a`): output-size + edge-list-
  read + endpoint-read trivial bounds.  Gap analysis shows
  TGT_TIGHT (sub-N+E) survives — L1.6 remains open.

### L1.6 (1) — first cost-bound graph-flavored benchmark E2E

`benchmarks/open_prbs/l16_bipartite_matching/bench_glover_verify.py`
(`27d2bb8`).  The first cost-bound graph-flavored benchmark
to synthesize end-to-end:
  - Template: a Loop processing edge endpoints with
    cost_target = `"n"`.
  - Synthesized: `cost@L = n - i`, τ includes `is_valid_pm`,
    Lean verifies via Tier-3 helper
    `sc7_fallthrough_62a3480b.solved.lean`.

**Honest framing.**  The algorithm is FULLY AXIOMATIZED via
UFs (`empty_matching`, `process_endpoint`) — this is NOT
algorithm discovery; the matching steps are hand-encoded as
uninterpreted operations with axiomatic semantics.  The real
value is validating that the cost-invariants infrastructure
(cost@L holes + cost-lb / cost-decrement / cost-budget
constraint kinds + Lean dispatch) works on graph-flavored
problems with quantified UF axioms.  Real algorithmic
discovery for matching is multi-week work — needs a graph
IR, list/array primitives, and new operations the current
IR doesn't have.  Banked in `COST_INVS.md` deferred section.

### Honest framework limits surfaced

1. **NIA tax on quadratic cost** (lesson #56).
   `bubble_sort_cost` pays 28s Z3-NIA on quadratic cost-
   decrement; a heuristic-routing slice that gates Lean-first
   dispatch on nonlinearity is documented but deferred.
2. **Generic Lean tactic chain insufficient for quantified
   UFs.**  `aesop`, `simp_all` don't instantiate quantified
   UF axioms cleanly — even "simple" matching benchmarks need
   Tier-3 helpers to close the cost-decrement obligation.
3. **L1.6 "synthesis" is an axiomatized shell.**  See above.

### Encoding lesson banked

**#56** (CLAUDE.md): COST_INVS NIA tax on quadratic cost
expressions.  Linear costs are free (Z3 dispatches in ms);
quadratic costs (cost@L_outer = (n-i) * K + ... where K is
itself a cost variable) trip NIA, paying ~12× over linear.
The fix is routing-side, not encoding-side: detect
nonlinearity in the cost atom and force Lean dispatch.
Deferred until a quadratic-cost benchmark becomes a measured
bottleneck.

### New benchmarks

- `benchmarks/cost_invs/sumi_cost.py`,
  `array_zero_cost.py`, `mul_cost.py`, `max_array_cost.py`,
  `nested_cost.py`, `bubble_sort_cost.py` — six cost-bound
  variants of foundation benchmarks.
- `benchmarks/cost_invs/sumi_cost_bad.py` — negative-only
  test (invalid candidates → UNSAT).
- `benchmarks/open_prbs/l16_bipartite_matching/` —
  `speculate.py`, `bench_glover_verify.py`, `REPORT.md`.
- `scratch/cost_invs_sum_array.py`,
  `scratch/cost_invs_nested.py` — design-validation
  scratch scripts.

### Status of north star #1

From design-only (where it sat in `COST_INVS.md` last week)
to substrate + first benchmark.  Two remaining infrastructure
gaps: (a) Recur cost@PROC composition; (b) SB(n>1) per-branch
cost variation.  Discovery on L1.6 itself still requires a
graph IR and primitive-operation library — multi-week work
out of scope for this push.

---

**Phase Tier-1 push — merge_two_sorted 6/7 promoted + IR-level
τ gating (2026-05-19).** 🎯

Today's session built on yesterday's 19 Tier-1 conversions
to push merge_two_sorted from 2/7 → 6/7 Tier-1, leaving only
the `merge_l2_entry_chain` ceiling.

Two-step strategy:

1. **f975af6**: Promoted 4 algorithmic axioms
   (`merge_branch0/1_preserves_inv`,
   `merge_l1_drain_b_preserves_inv`,
   `merge_l2_drain_a_preserves_inv`) to Tier-1 theorems
   using `is_sorted_*` aux lemmas plus 2 focused boundary
   axioms (`merge_array_boundary_A/B`) for the i'=n / j'=p
   edge case.

2. **306400b**: IR-level fix — gated τ atoms 5/6 on
   `i<n`/`j<p`.  At the boundary the gated antecedent fails
   and the atom is vacuously true.  Eliminated the 2 focused
   boundary axioms.  Proofs became simpler (no boundary
   case-split).

Net: merge axioms went from 4 algorithmic + 2 boundary + 1
ceiling = 7 down to 6 Tier-1 theorems + 1 ceiling.

**Encoding lessons banked from this session**:

54. **Tier-2-first authoring is even better when boundary
    cases are isolable.**  The 4 merge per-step helpers
    hit a boundary case (A[n] / B[p] unconstrained by
    is_sorted up to n / p).  Two paths: (a) add focused
    boundary axioms that capture the gap in 2 one-liners
    (intermediate Tier-2 result); (b) gate the τ atom at the
    IR level to make the boundary vacuous (full Tier-1).
    Both have merit — (a) lands faster + smaller proofs;
    (b) is cleaner trust.  Doing (a) first then (b) gave us
    an incremental commit history that's easy to revert.

55. **The chain-aware abstract Loop transition is the
    precision limit for `merge_l2_entry_chain`.**  Even with
    gated τ, the abstract L1 transition doesn't preserve C
    between s2 (L0 exit) and s3 (L1 entry).  L1's body
    modifies C, so the frame eqs don't include C.  Therefore
    the L1 transition admits any C_s3 satisfying τ@L1 at
    s3 — including ones where C_s3[i+j-1] > A_s3[i_s3].
    The conclusion `C_s3[i+j-1] ≤ A_s3[i_s3]` can't be
    derived from the chain hypotheses alone.  Promoting
    this would require a strengthened abstract Loop
    transition that propagates more relational info.

56. **COST_INVS overhead is dominated by Z3-NIA on quadratic
    cost expressions.**  Across 6 measured (baseline, cost-
    variant) pairs:

      | Cost shape   | Overhead range |
      | ---          | ---            |
      | LINEAR cost  | 0.03x – 0.22x  (cheap; sometimes faster) |
      | QUADRATIC    | 12.34x         (Z3-NIA tax on bubble_sort) |

    Mechanism: cost-decrement `cost@L(pre) ≥ body_cost +
    cost@L(post)` becomes a polynomial-arithmetic check when
    cost@L is quadratic.  Z3's NIA heuristics handle it but
    slowly.  Linear cost expressions stay in QF_LIA and impose
    no measurable cost beyond extra constraints.

    **Implication**: targeting linear cost bounds (e.g., L1.6's
    O(E + V log V) family, L3.4's O(constant) SLP lengths) is
    in the cheap regime.  Targeting quadratic+ bounds (e.g.,
    arbitrary algorithm-complexity claims) pays a real tax.
    The NIA wall is the practical reach limit.

---

**Phase H.4 — cardinality-ordered enum + floyd_warshall E2E +
insertion_sort helper: DONE (2026-05-19).** 🎯 **MILESTONE.**

Three layered optimizations + one helper, on
`experimental/cardinality-ordered-enum` branch (to be merged
to main after CI):

1. **Cache-only Lean for `ranking-*`** (`solver.py`).
   Skips the 5-15s `lake env lean` generic-chain call for
   ranking obligations.  Still consults curated `.solved.lean`
   companions.  Eliminates noise from FW v3's ranking-lb
   enumeration without losing soundness.

2. **Cardinality-ordered enumeration with monotone pruning**
   (`solver.py`).  For `ranking-*` with |τ| ≥ 10 and same-
   position free τ holes, enumerate by ascending (ANT) /
   descending (CONS) cardinality, stop at first valid.  Emit
   a cube pinning only the minimal atoms; supersets implicit.
   Gates via `_classify_atoms` + `_free_tau_position` (see
   SOUNDNESS.md "Cardinality-ordered enumeration ...").

3. **General helper short-circuit on Z3 path** (`solver.py`).
   The §H.2.CODEGEN short-circuit was previously gated on the
   axiom-heavy Lean dispatch.  Lifted to fire before any
   enumeration when helper_registry is set.  insertion_sort
   (no UF/axioms) now hits it for its nested chain-bundle
   obligation.

4. **`insertion_sort_l1_body_inductive_chain`** — new Tier-2
   axiom in `lean/SynthLean/Y2Corpus/insertion_sort/Helpers.lean`.
   Covers the L0 inductive when the chain-aware bundle-post
   translator routes there.  Required after the #167
   translator fix exposed an obligation that previously
   errored out fast.

**E2E timings (experimental branch)**:

| Benchmark        | Pre-opt        | Post-opt   | Speedup        |
| ---              | ---            | ---        | ---            |
| `floyd_warshall` | 40+ min wedge  | **<60s**   | E2E unlocked   |
| `insertion_sort` | 412s           | **6.5s**   | 63×            |
| `sum_array`      | 107s           | 102s       | unchanged      |
| `merge_two_sorted` | ~2 min       | unchanged  | path not hit   |

Quick regression on experimental: **72/72 passed**, no
soundness regressions, no count mismatches.

**Soft timing-drift detection** also landed.
`tests/regression_timings.json` captures baseline elapsed per
benchmark; regression prints `[SLOW: N.Nx baseline]` /
`[FAST: N.Nx baseline]` annotations when current deviates ≥
1.5× or ≤ 0.5×.  Final summary lists drifts.  Doesn't affect
pass/fail (CI machines vary); informational.

**Lessons banked (#51, #52, #53)**:

51. **Cache-only Lean for ranking-* is the cheap win;
    cardinality is the heavy lift; both are needed.** Each
    alone is insufficient: cache-only eliminates noise but
    leaves enumeration cost; cardinality cuts enumeration but
    inflates per-check cost on axiom-heavy benchmarks (UF
    E-matching gets stuck on single-atom subsets).  The
    composition wins when you ALSO gate cardinality on |τ|≥10
    so axiom-heavy benchmarks with small τ stay on the
    original path.

52. **Translator extensions can quietly regress benchmarks.**
    The nested chain-bundle support (commit 2b164b4 — added
    for FW) enabled `safety-bundle-post` translation on
    obligations that previously errored out fast with
    NotImplementedError.  insertion_sort's sc5 fell into this
    newly-translatable case → generic tactic chain → 60+
    UNKNOWN dispatches → 412s wall.  Diagnosis required
    bisecting against main, not just experimental-vs-baseline.
    Mitigation: a Tier-2 helper for the nested obligation,
    short-circuiting via the lifted helper fast path.

53. **Soft timing-drift detection in regression** surfaces
    perf regressions during the run rather than requiring a
    rerun on main.  Cost: a JSON file with last-known
    baselines + ~30 LOC of comparison logic.  CI machines
    vary, so the check is soft (informational annotation only).

---

**Phase #167 — chain-aware translator extensions +
merge_two_sorted E2E: DONE (2026-05-19).** 🎯 **MILESTONE.**

Translator support for benchmarks whose bundle-entry /
bundle-post constraints span CHAINED loops (e.g.
`SB >> Loop(L0) >> Loop(L1) >> Loop(L2)` in merge_two_sorted)
or NESTED loops (e.g. FW's triple-nested DP).  Previous flat
translator (`theorem_for_entry_bundle` / `theorem_for_chain_bundle`)
raised `NotImplementedError: no SB(init) block found` whenever
the chain contained a non-SB item.

**What landed:**

1. **`_linearize_path(template, target_loop_id)`** in
   `synth/lean_backend/translate.py` — returns
   `(chain_items, target_idx, enclosing_loop_id)`.  Handles
   both top-level chains (enclosing_loop_id=None) and nested
   targets (enclosing_loop_id=<outer loop_id>).
2. **`_chain_state_binders` + `_emit_chain_item_hyps`** —
   per-state binder naming `<var>_s<k>` (k=0..target_idx).
   SB items → trans + frame hypotheses; Loop items →
   abstract `τ_inner` + `¬g` + frame eqs.
3. **`theorem_for_entry_bundle_chain`** — chain-aware bundle-
   entry: walks the chain up to target, asserts target's τ
   atoms at state[target_idx].
4. **`theorem_for_chain_bundle_chain`** — chain-aware bundle-
   post: walks the full chain (target_idx+1 abstract trans),
   asserts the user post at the final state.
5. **`verify.py` dispatch** — routes to chain-aware translator
   when `chain[:target_idx]` has non-SB items OR
   `enclosing_loop_id != None`; otherwise stays on flat.

**E2E validation: merge_two_sorted** — the bellwether multi-
loop chain benchmark.  Pre-#167: wedged with 188 sc7
fallthrough dumps in 10+ min (flat translator raised
NotImplementedError on every bundle obligation).  Post-#167
with 3 chain-aware Tier-2 axioms (`merge_l1_entry_chain`,
`merge_l2_entry_chain`, `merge_final_post_chain`):
**~2 min, 1 solution**.  Synthesizes the classical 4-phase
merge:

    init i=j=0;
    while (i<n ∧ j<p):  if A[i]≤B[j] emit A[i],i++; else emit B[j],j++
    while (j<p):        emit B[j], j++         // drain B
    while (i<n):        emit A[i], i++         // drain A

**FW E2E: not yet** — the chain-aware translator routes FW's
bundle obligations correctly (verified by 22 sc1 fallthrough
dumps, all showing the new shape with `h_enc_tau_*` enclosing-
τ binders).  But FW needs more chain-aware Tier-2 axioms
(L1 entry, L1 post, L2 entry, L2 post, plus the inner / middle
inductives) for E2E synth to close.  Deferred to a future
session.

**Encoding lesson banked (#46, #47):**

46. **Chain-aware vs flat translator dispatch.**  Earlier
    translators assumed each bundle-entry obligation's chain
    started with an SB(init) block: `SB(B0) >> SB(B1) >> ...`.
    Real benchmarks (merge_two_sorted, FW) have chains with
    embedded Loops or nested Loops.  The fix is structural:
    a SEPARATE chain-aware translator family with per-state
    binders (`<var>_s<k>`) instead of pre/post bindings.  The
    flat path stays for benchmarks that fit its assumptions
    (single-loop SB-only chains) — no perf regression.

47. **Smoke-testing chain-aware verify needs FULL chosen_atoms.**
    When debugging via `verify_class_via_lean` directly, the
    `chosen_atoms` dict MUST include all `s@*` / `g@*` /
    `phi@*` picks (not just τ subsets) — otherwise the
    translator emits frame eqs instead of trans hypotheses
    for missing SBs, producing different binder names than
    the cite expects.  Also: `expand(problem)` must run
    before `verify_class_via_lean` so `Loop.loop_id` fields
    are populated (otherwise `_linearize_path` returns None
    and dispatch silently falls back to the flat translator
    which then crashes with NotImplementedError).

**Tasks #172-#176 closed.**  Task #155 (merge_two_sorted E2E)
closed.

---

**Phase H.2.CODEGEN — helper-citation codegen + 3 single-loop
stretch benchmarks E2E: DONE (2026-05-19).** 🎯 **MILESTONE.**

The codegen direction (RESEARCH.md §H.2.CODEGEN) is now
validated end-to-end across three stretch benchmarks.  All
three previously timed out or UNSAT'd; all now synthesize
verified solutions in 70s-3min.

| Benchmark | Pre-codegen | Post-codegen | Speedup |
| --- | --- | --- | --- |
| `kadane_max_subarray` | 600s timeout | **70s** | 8.5× |
| `modular_exponentiation` | 1800s timeout | **70s** | 25× |
| `majority_element` | UNSAT (1487s) | **3min** | works |

Each synthesizes the canonical algorithm:
  - kadane: extending-vs-restarting two-branch.
  - modexp: repeated squaring (odd/even branches).
  - majority: Boyer-Moore voting.

**What landed (chronological)**:

  1. **§H.2 codegen module** (`synth/lean_backend/codegen.py`).
     HelperRegistry + HelperEntry + try_helper_citation +
     _attach_indices + _make_hyp_for.  Structural plumbing
     only — translates `(sc_kind, loop_id, branch_idx,
     chosen_atoms)` to a `:= by exact <helper> <args>` proof
     body.  Boundary: helpers carry the math; codegen carries
     the citation glue.  Driver-LLM uninvolved by
     construction.

  2. **FW Lean artifact fully proved** (modulo ONE Tier-2
     axiom `sp_self_nonneg`, the non-neg-cycles assumption).
     sp_k_row_preserved / sp_k_col_preserved / inner inductive
     all converted from axioms to theorems.  Inner inductive
     proof ~80 lines using D↔sp lemmas + branch case analysis.
     `Problem.pre` augmented with matching non-neg-cycles
     hypothesis.

  3. **Translator extensions**:
       - `theorem_for_chain_bundle` accepts loops with non-SB
         bodies (FW's L0 has Seq body with nested loops) via
         `_modified_vars_of_template`.
       - `theorem_for_coverage` (new) — handles SB(n>1)
         coverage obligations.  Replaces Z3-with-axioms path
         (which produces spurious UNKNOWNs on quantified UF
         atoms) with Lean's `omega`/`decide`.

  4. **Helper short-circuit** (solver.py).  When
     `helper_registry.find(...)` matches the FULL τ subset
     AND `verify_class_via_lean` returns valid, emit ONLY the
     full-τ cube and SKIP per-subset enumeration.  Drops
     2^|τ| dispatches to 1 per matched constraint.  Sound: each
     cube is helper-proved (no over-generalization).
     Completeness tradeoff: smaller τ subsets skipped, so
     synthesized solutions carry full τ (score not minimized).

  5. **Monotonicity fast-path on Lean dispatch** (solver.py).
     Phase 3.L's structural property of conjunctive τ
     (ANT-only → empty hardest; CONS-only → full hardest)
     applies regardless of verifier.  Re-enabled on the Lean
     path; dispatches 1 instead of 2^|free-τ| for
     single-position holes.

  6. **Coverage Lean translator** (`theorem_for_coverage`).
     Emits `Pre ∧ τ ∧ g_loop ⇒ ⋁ g_branch`.  Tactic chain:
     `omega | nlinarith | decide | simp_all | aesop |
     by_contra+omega`.  Routes coverage through Lean for
     axiom-heavy benchmarks.

  7. **`_AXIOM_HEAVY_DISPATCH_KINDS` = {safety,
     safety-bundle-entry, safety-bundle-post, coverage}**.
     ranking-* STAYS ON Z3 (linear arithmetic, Lean process
     contention caused regression — see Lesson #46 below).

  8. **Per-benchmark wiring**:
       - `floyd_warshall.py`: bundle-post helper registered.
         E2E blocked on nested-loop translator extension
         (task #167).
       - `kadane_max_subarray.py`: bundle-post + 2 safety
         branch helpers.  E2E: 70s.
       - `majority_element.py`: bundle-post + 2 safety branch
         helpers (boyer_moore_dominance + bm_inv axioms).
         E2E: 3min.
       - `modular_exponentiation.py`: bundle-post + 2 safety
         branch helpers (modexp_branchN_preserves_inv axioms).
         E2E: 70s.

  9. **`_LEAN_PARALLEL_WORKERS` bumped** from `cpu_count // 2`
     to `cpu_count` (8 on a typical Mac).  Helps the codegen
     path's parallel dispatch.

  10. **`_on_z3_sat` skips ranking-* cross-check**.  When Z3
      SAT-refutes a ranking obligation, trust Z3 directly
      (rankings are linear).  Was emitting spurious dumps on
      empty-τ ranking-lb subsets where Lean's omega (without
      τ premises) couldn't prove the goal.

**Encoding lessons banked from H.2.CODEGEN**:

45. **Codegen as STRUCTURAL plumbing, not semantic proof
    writer.**  The earlier rejection of codegen ("driver-LLM
    will write shims later") conflated two distinct codegens:
    semantic-proof codegen (rightly rejected — LLM territory)
    vs structural-wrapper codegen (purely mechanical citation
    glue derived from `(sc_kind, chosen_atoms, helper_name)`
    — not LLM territory).  The latter is what the translator
    already does today when emitting `.failed.lean` dumps;
    swapping the proof body for `:= by exact <helper> <args>`
    is the same plumbing.  This boundary makes the codegen
    module ammortizable across benchmarks without conflicting
    with future driver-LLM (Phase Y.2).

46. **ranking-* on Lean dispatch causes wall-clock blowup
    from process contention.**  Initial speedup attempt put
    ranking constraints on Lean path (same routing as safety).
    Result: kadane v5 / modexp v5 hit 10-min timeout despite
    cpu_count=8 workers.  Effective parallelism was ~1.1× —
    lake/lean process startup serializes on something (mathlib
    olean loading?  lake's file locking?).  Lesson: linear
    obligations stay on Z3 even when the benchmark is
    otherwise axiom-heavy.  Z3 returns SAT (refuted) for
    invalid empty-τ on rankings; the per-subset enumeration
    then finds valid subsets cheaply.

47. **Coverage with quantified UF axioms in scope → Z3
    UNKNOWN-rejection.**  majority's coverage check (`cnt = 0
    ∨ cnt > 0`) is trivially provable from `cnt ≥ 0` (atom
    2).  But Z3's verifier carries the `count_eq` universal
    axioms, and quantifier instantiation could return UNKNOWN
    on the coverage check.  Under sound mode the full-τ
    coverage cube got UNKNOWN-rejected → coverage's cube list
    lacked full τ → SAT inconsistent with safety constraints'
    full-τ requirement → UNSAT.  Fix: route coverage through
    Lean (omega/decide closes without UF interference).
    Coverage is a new translatable kind in
    `_LEAN_TRANSLATABLE_KINDS`.

48. **Helper short-circuit: sound narrower, not unsound
    broader.**  Two superficially similar shortcuts have
    OPPOSITE soundness properties:
      - H.2.PROTOTYPE: "all-True validates → ALL 2^|τ| subsets
        valid → mark every cube valid".  UNSOUND for
        BOTH-position with distractor atoms.
      - H.2.CODEGEN short-circuit: "helper validates FULL τ →
        emit ONLY THE FULL-τ CUBE".  SOUND — same trust as
        any helper citation.  Loses score-minimization
        (synthesized solution carries full τ), not soundness.
    The information flow distinguishes them: the prototype
    generalized (unsound); the short-circuit just emits the
    specific subset it proves (sound).

49. **`_on_z3_sat` cross-check is selective.**  When Z3 SAT
    is genuinely reliable (linear arithmetic, no axioms used),
    cross-checking via Lean introduces noise.  For ranking
    kinds: Z3 SAT on empty-τ ranking-lb is correctly invalid;
    Lean would error trying to prove (omega lacks premises).
    The cross-check was meant for axiom-heavy obligations
    where Z3's quantifier instantiation might miss an axiom
    instance.  Adding a kind allowlist (ranking-* skipped)
    fixed the spurious dumps.

50. **Coverage of helper short-circuit varies by benchmark.**
    For kadane: bundle-post + 2 safety branches matched → 3
    short-circuit fires.  For majority: same, plus the
    additional safety axioms cite boyer_moore_dominance
    via Tier-2.  For modexp: same, plus modexp_branchN
    axioms.  Helper coverage in synthesized hint:
    `Helper coverage: X/Y dispatches via Tier-3 helper`.
    A new "headline" metric for per-benchmark coverage.

**Future work tracked**:
  - Task #167: FW nested-loop translator extensions
    (multi-day; FW E2E blocked).
  - Task #170: Per-atom helpers for safety inductives
    (DEFERRED — score-minimization only, no correctness gain).

---

**Phase X.S — stretch corpus (IN PROGRESS, 2026-05-17 → ongoing).**
10 benchmarks beyond the basics, plus 3 discrimination tests and 1
edge-of-open research benchmark.

**Verified (5):**
- `karatsuba_deg2` (Z3 alone, ~5s) — 3-mult deg-1 poly mult.
- `toom3_deg2` (Z3 alone, ~5s) — 5-mult deg-2 poly mult; Z3 handles
  polynomial-identity divisibility under `//` automatically.
- `boolean_matmul_3x3` (Z3 alone, ~5s) — naive 27-AND 18-OR.
- `binary_search` (Z3 alone, ~30s) — 3-phase template after the
  found-flag pattern failed.  Surfaced a real capability gap
  (loop ranking-decrease vs found-flag); banked in CS-5.
- `strassen_3x3_laderman` (Z3 alone, <60s) — Laderman 23-mult.
  First edge-of-open result.  Formulas solved by sympy linear
  algebra over the 81 a_pq*b_rs basis; verified across 100
  random integer trials before synth.

**Lean-curated (3):**
- `modular_exponentiation`: 16 `.solved.lean` (Tier-1 helper
  `pow_mod_base`).  Synth re-run pending.
- `majority_element`: 16 `.solved.lean` (Tier-2 helper
  `bm_inv_preserve_b0/b1` — Boyer-Moore's classical inductive
  step encapsulated as axiom because the user's τ-atom set
  doesn't carry the proof through).  Synth re-run pending.
- `kadane_max_subarray`: 56 sc0 + 11 sc2 + 6 sc2-invalid
  `.solved.lean` / `.invalid.lean` companions.  6 dumps are
  GENUINELY-INVALID τ subsets (missing `cur_ub`; documented
  with concrete counter-example).  Synth re-run in progress.

**Discrimination tests (3, all DISCRIM-PASS):**
- `karatsuba_deg2_discrim_2mult` — 4 representative 2-mult
  candidates, all UNSAT.  Confirms framework's 3-mult lower
  bound recognition.
- `toom3_deg2_discrim_wrong_coef` — `// 3` instead of `// 2`
  in r2 interpolation; correctly UNSAT.
- `strassen_3x3_lt23mult_search` (NEW research benchmark) —
  23 hand-crafted 22-product candidates (each dropping one of
  Laderman's m_i with best-effort output formulas).  All
  UNSAT, confirming our discrimination works AND surfacing
  that real discovery needs IR support for parametric m_i
  templates (banked in RESEARCH.md §G.5).

**Untested / xfail at edges (4):**
- `merge_two_sorted` — refactored to 4-phase template after
  the original (single loop with overlapping guards) hit
  per-class-valid-but-globally-inconsistent.  Untested.
- `modular_exponentiation`, `majority_element` — Lean-curated
  but synth re-run timed out at our test budget; need a fresh
  attempt with longer budget.
- `edit_distance`, `floyd_warshall` — incomplete τ atoms in
  source; deferred (their structural shape requires careful
  invariant design we haven't done yet).

**Helper-axiom trust tiers (2026-05-17 finding):**
- **Tier 1**: local derivable lemma — provable from user
  axioms by short induction (e.g., `pow_mod_base`).  Trust
  the math; document the derivation.
- **Tier 2**: inductive-step encapsulation — the helper IS
  the proof obligation itself (e.g., `bm_inv_preserve_b0/b1`).
  Effectively a "trust the algorithm is correct" claim.
  **Tier-2 helpers are a signal the user's τ atoms are too
  weak to be self-inductive.**  Documented in problem.skill
  and EXPERIENCE_REPORT CS-6.

**Codegen for repetitive proofs (2026-05-17 finding):**
When N `.solved.lean` files share a structural template, write
a Python script generating them from a parameterized table
(see `/tmp/majgen.py`, `/tmp/kadanegen.py`).  Used for 12 of
16 majority_element companions, all 56 kadane sc0, and 11
kadane sc2.

Full design rationale in **`RESEARCH.md` §D.1.5**.
Edge-of-open extensions banked in **`RESEARCH.md` §G.5**.
Curation case studies in **`EXPERIENCE_REPORT.md` CS-5, CS-6**.

---

**Phase X — benchmark scaling + corpus building (TARGET HIT,
2026-05-18).**

50 corpus benchmarks committed across 9 batches.  Each carries
an explicit English `description` (top-of-file docstring as the
user would phrase the spec) and is part of either the quick
suite (66 benchmarks) or slow suite (11 axiom-heavy benchmarks).

Batch summary:
  - **Batch 1** (5): min_array, array_fill, array_copy,
    increment_array, negate_array.
  - **Batch 2** (9): max2, add_arrays, clamp_array_positive,
    array_double, subtract_arrays, min_index, array_swap,
    linear_combination, pairwise_max.
  - **Batch 3** (3 axiom-heavy): factorial, count_zeros,
    array_product.
  - **Batch 4** (7): max3, abs_diff, last_element, mid3,
    swap_first_last, scalar_clamp, range_init.
  - **Batch 5** (4): abs_array, saturate_add, max_min_diff,
    array_max_index.
  - **Batch 6** (5): array_increment_at, all_positive,
    array_set_const, scalar_max4, count_equal.
  - **Batch 7** (8): array_concat, find_first_pos,
    min_max_pair, array_rotate_left, array_shift_right,
    dot_product, sum_first_k, array_neg_count.
  - **Batch 8** (7): array_max_val, array_min_val, abs2,
    sign, range_init_offset, gcd, power_of_two.
  - **Batch 9** (5): reverse_array, is_sorted, scalar_min4,
    clamp_array_range, array_index_of.

Axiom-heavy benchmarks (11 total in slow suite) all sound by
default with curated `.solved.lean` companions under
`lean/SynthLean/Y2Corpus/`.  Templates: `factorial`, `fib`,
`sum_array`, `array_product`, `count_zeros`, `count_equal`,
`dot_product`, `sum_first_k`, `array_neg_count`, `gcd`,
`power_of_two`.

**Phase Y.1.5 hash CLI (DONE).**  `python -m
synth.lean_backend.hash <benchmark.py>` prints `(sc_idx, kind,
branch_idx, signature_hash, expected_filename)` for every
soundness-critical constraint.  Replaces the 5x copy-paste
recipe curators used in batches 3-5.  See EXPERIENCE_REPORT CS-4.

**Nightly CI (DONE).**  `.github/workflows/nightly.yml` runs the
slow regression daily at midnight UTC (workflow_dispatch for
manual triggers).  60-min `concurrency` group separate from
main CI so the two don't preempt each other.

**Reverse-array curation note (banked).**  The ranking-LB
constraint `τ ⇒ ϕ ≥ 0` must hold at EVERY τ-consistent state,
including loop-entry states where the guard is false (loop
doesn't execute).  For `reverse_array` at n=0 the entry has
lo=0, hi=-1, which makes the natural `ϕ = hi - lo` negative.
Fix: use `ϕ = hi - lo + 1` (≥ 0 at the edge, still strictly
decreasing).  Worth keeping in mind when authoring loops that
might run zero iterations.

**Phase Y.1.5 — sound-by-default for axiom-heavy benchmarks
(DONE, 2026-05-17).**  All five axiom-heavy benchmarks
(`fib`, `factorial`, `sum_array`, `array_product`,
`count_zeros`) now synthesize under `potentially_unsound = False`.

Architecture: chain-bundle Lean translator
(`theorem_for_entry_bundle` + `theorem_for_chain_bundle`)
extends Lean dispatch to safety-bundle obligations that Z3
can't reliably handle.  Per-branch dispatch (`branch_idx` on
SafetyConstraint) handles SB(n>1) loop bodies.  Curated
`.solved.lean` files under `lean/SynthLean/Y2Corpus/<bench>/`
prove the axiom-heavy obligations the generic tactic chain
can't close.  Lenient fallback EXCISED — `Problem.potentially_unsound`
field remains as a documented dev escape hatch but its
production code path is dead.  CI grep enforces no benchmark
sets it to True.  See `SOUNDNESS.md` for the full posture.

**Lean-dispatch regression signal (Phase X complementary, 2026-05-16).**
`Problem.expected_lean_hits: int | None = None` field added.
The subprocess regression helper (`_solve_one.py`) emits
`lean_dispatch: {valid, unknown, errors}` per benchmark;
`regression.py` checks `lean_dispatch.valid` against the
expected.  Catches:
  - **Tactic regressions**: a translator change makes
    obligations Lean used to prove stop closing.
  - **Silent capability improvements**: a tactic fix raises
    the count — bump the expected to lock in the win.

All 34 existing benchmarks annotated.  Most (Z3-decidable) =
0; `sum_array` = 2 (Lean closes 2 of ~7 UNKNOWN classes);
`fib` = 0 currently.  Display format
`[Lean: N✓ N?, N✗]` shows up only when Lean fires.

**Y2 corpus: mechanically-checked (failed, companion) pairs
(Phase X complementary, 2026-05-17).**  Per-benchmark
subdirectories under `lean/SynthLean/Y2Corpus/<benchmark>/`
collect (`.failed.lean`, `.invalid.lean` | `.solved.lean`)
**triples** for the Phase Y.2 driver-LLM training data.

  - `.failed.lean` — auto-dumped by
    `synth.lean_backend.verify._dump_failed_obligation` when
    Lean's generic tactic chain can't close an obligation in
    its timeout budget (per-benchmark dump dir set via
    `Problem.dump_lean_failures_dir`).  Never hand-edited.
  - `.solved.lean` — hand-written Lean theorem proving the
    same obligation.  Curators write these when the obligation
    is actually provable but generic tactics aren't strong
    enough.
  - `.invalid.lean` — Lean theorem of the form
    `∃ <vars>, <hyps> ∧ ¬ <goal>` — a **mechanically-verified
    existential counterexample**.  Curators write these when
    the τ subset is genuinely insufficient (synthesizer
    correctly rejects it).

Why mechanically-checked: a prose comment claiming invalidity
is unverifiable; a Lean proof of the negation is.  CI runs
`tests/test_y2corpus.py` which invokes `lake env lean` on
every committed companion.  See `lean/SynthLean/Y2Corpus/README.md`
for the protocol and current entries.

**Protocol for adding to the corpus.**  Per benchmark:

  1. Set `dump_lean_failures_dir =
     "lean/SynthLean/Y2Corpus/<benchmark>"` on the `Problem`.
  2. Run the benchmark.  Failed classes auto-dump as
     `<theorem_name>_class_<N>.failed.lean`.
  3. Inspect each dump.  Decide: provable-but-hard (write
     `.solved.lean`) or genuinely-invalid τ subset (write
     `.invalid.lean` as `∃ ..., hyps ∧ ¬ goal`).
  4. Companion goes alongside the dump in the same subdir,
     same `<stem>`, with the appropriate suffix.
  5. Verify locally: `tests/test_y2corpus.py` runs
     `lake env lean` on every committed companion.
  6. Commit `.failed.lean` and its companion together.

For Phase Y.2 driver-LLM training, the corpus is a multi-shot
ICL example bank: failed → solved teaches "here's how to prove
this kind of obligation"; failed → invalid teaches "recognize
genuine τ insufficiency, signal back to the outer loop".

**Phase 1 — End-to-end Python synthesizer: DONE (2026-05-11).** The
`synth/` package implements IR (`ir.py`), expansion (`expand.py`),
single-hole single-atom constraint generation (`constraints.py`),
expression parser (`expr.py`), solver loop with top-K enumeration
(`solver.py`), three-outcome result types (`result.py`),
pretty-printing decoder (`decode.py`), textual+JSON parsers
(`parse.py`), and a CLI (`cli.py`, `python -m synth`). Editable
install via `pyproject.toml`.

All four planned benchmarks pass through the new pipeline:
`benchmarks/intsqrt.py` (single-loop, picks POPL'10 Eq. (7) solution),
`benchmarks/sumi.py` (single-loop, `2s = i(i+1)` invariant),
`benchmarks/swap.py` (acyclic only), `benchmarks/strassen.py`
(acyclic with polynomial identity; Z3 returns both naive 8-mult and
Strassen 7-mult). Failure-channel test in
`tests/test_failure_channels.py` validates §6.2 telemetry — UNSAT
returns `NoSolution` with `unsat_core` and `hints`.

**Encoding lessons banked from Phase 1:**

1. **Two transition-atom formats supported (since Phase 1.5):**
   - **Parallel** (`dict[str, str]`) — POPL'10 §3.1 style. RHS parses
     against pre-state only; vars not in the dict are preserved.
   - **SSA / sequential** (`list[{var: rhs}]`) — PLDI'11 / Pragna
     `SymbolicExecutor` style. Each entry assigns one variable; later
     entries may reference earlier LHS. Intermediates (e.g. Strassen's
     `v_i`) are first-class. Implemented by *symbolic substitution*
     at constraint-generation time — no fresh Z3 names appear in the
     output formula. See `synth/constraints.py:_trans_body`.

2. **POPL'10's `r_l = ϕ_l` tracker is unnecessary in Z3** (Phase 0
   lesson; carried forward). Decrease is just
   `ϕ(unprimed) > ϕ(primed)`.

3. **Cross-block intermediate threading not yet supported.** Within
   one SB block, SSA handles intermediates. Across consecutive SB
   blocks (e.g. `SB; SB`) the constraint generator still raises
   `NotImplementedError`. Pending whenever a benchmark needs it.

**Phase 2 — Conjunctive holes in invariant templates: DONE (2026-05-11).**
`tau@*` holes now use *conjunctive* dispatch — each atomic predicate is
independently selected via its indicator; the chosen subset is conjoined
(`synth/constraints.py:_conj_hole`).  No single-hot constraint on
`tau` indicators (so 2^|P| subsets are searched).  Guards / ranking /
transitions stay single-hot.

User-facing change: τ atoms should be **atomic** predicates, not
pre-composed conjunctions.  IntSqrt, Σi, mul, and the failure-channel
test all run under the new encoding; existing acyclic benchmarks
(swap, strassen) are unaffected (no τ holes).  Σi and mul both return
multiple valid solutions where the lower-score one *drops redundant
atoms* — direct evidence that Phase 2 search is doing real work.

**Encoding lessons banked from Phase 2:**

4. **Atomic atoms beat composite atoms under conjunctive dispatch.**
   Z3 returns `unknown` in ~1s on quadratic-arithmetic problems when
   τ's candidate atoms are themselves composite predicates (each atom
   = nested AND of comparisons).  Same problem with atomic atoms
   resolves in ms.  Workaround: write atoms as atomic predicates.

**Phase 2.5 — `SB(n>1)` for conditional branches: DONE (2026-05-11).**
Acyclic blocks can now have multiple guarded transitions, decoded as
`if / else-if / else` chains.  Hole naming under SB(n>1):
`s@B0.0…s@B0.{n-1}` for transitions, `g@B0.0…g@B0.{n-2}` for guards
(last branch's guard is the implicit "else" — `⋀ ¬g_j` over earlier
guards).  Disjunction-of-guards tautology is automatic; the encoding
guarantees mutual exclusion via cumulative-else semantics, so the
constraint generator emits one path per branch.

Two new acyclic benchmarks pass: `benchmarks/abs.py` (3 valid solutions
for `y = |x|`: `x<0/else`, `x>0/else`, `x<=0/else`), and
`benchmarks/sat_sub.py` (3 valid solutions for `r = max(0, a-b)`).

**Encoding lesson banked from Phase 2.5:**

5. **Spurious `BoolVal(True)` in `And()` antecedents wrecks Z3's NRA
   heuristic.** First version of `branch_paths` for SB(n=1) emitted
   `And(τ, g, True, s) ⇒ τ'`.  Z3 returned `unknown` in 1.3s on Σi
   (quadratic invariant `2s = i(i+1)`) regardless of timeout budget.
   Removing the explicit `True` (passing `None` for the trivial guard
   and conditionally omitting it from the conjunction) restored
   sub-second SAT.  Z3 does *not* always simplify `And(…, True, …)`
   before running quantifier-elimination tactics — keep antecedents
   tight.

**Phase 3 (first cut: A + B + C + CEGIS): DONE (2026-05-11).**
Three sub-phases plus a major architecture change:

- **Phase 3.A** — Array-typed program variables. `Var(name, "int[]")`
  maps to `z3.Array(Int, Int)`; `A[k]` reads parse to `z3.Select`.
- **Phase 3.B** — Quantified atoms via Python-lambda syntax:
  `"ForAll(lambda k: Implies(0 <= k and k < i, A[k] <= m))"`.  Multi-
  arg lambdas (`lambda k, j: …`) and `Exists` are also supported.  The
  parser opens a fresh binding scope for the lambda's bound variables;
  all bound vars default to `IntSort`.  Encoding lives in
  `synth/expr.py:_translate_call`.
- **Phase 3.C** — Array writes via `Update(A, i, v)` → `z3.Store`.
- **CEGIS refactor** — `synth/constraints.py:generate` now returns
  *unwrapped* `SafetyConstraint(body, quantified_vars)` records rather
  than top-level `ForAll(V, body)` assertions.  `synth/solver.py`
  drives a CEGIS loop: main solver searches indicators (Boolean only);
  per-iteration, substitute indicator values into each safety body and
  ask Z3 whether `Not(body)` has a model (counter-example).  If yes,
  block the bad indicator assignment; if no for every body, record a
  solution.

Three new benchmarks pass: `benchmarks/max_array.py` (single loop +
if/else + quantified invariant; 5 solutions including ones that
exploit the spec's weakness — see lesson #6), `benchmarks/array_zero.py`
(loop with array update; 2 solutions, with vs without redundant
`0 <= i`).

All 7 previously-passing benchmarks still pass under CEGIS.

**Encoding lessons banked from Phase 3:**

6. **Z3 is decisive for SAT, indecisive for proving validity.** First
   attempt at max_array returned `unknown` instantly regardless of
   timeout, tactic chain, or explicit patterns.  Z3's quantifier
   reasoning cannot prove `∀V. (∀k. P(k, V)) ⇒ Q(V)` directly even
   when it's valid (verified: the negation is correctly `unsat`).  The
   fix is the standard CEGIS pattern — never ask Z3 to prove validity;
   ask it to find counter-examples (a SAT question) and block bad
   candidates.  This is also how POPL'10's predicate-abstraction
   reduction works under the hood.

7. **Underspecified specs admit weak solutions.** `max_array`'s post
   `∀k. A[k] ≤ m` is satisfied by `m = INT_MAX` or any upper bound;
   solutions #0/#1 initialize `m := 0` and only update on `A[i] >= m`
   (or never, for all-negative arrays).  Spec-strengthening with
   `m ∈ {A[k] | k < n}` (existential) or an axiom like
   `m == max-of(A, n)` would force the "real" max.  Worth noting when
   reviewing LLM-supplied specs.

**Phase 3.D — uninterpreted functions + axioms: DONE (2026-05-11).**

API additions:
- `Problem.uninterpreted: list[(name, [arg_types], return_type)]` —
  declarations registered as `z3.Function` in the constraint generator
  and passed through a `uf` registry to `parse_expr`.
- `Problem.axioms: list[str]` — expression strings parsed against the
  pre-binding (with the same `uf` registry); the CEGIS verifier asserts
  every axiom *before* the negated body, so counter-example search
  respects them.
- `expr.py` falls through unknown `Call` names to the `uf` registry,
  applying `z3.Function`.  Quantifier scope plus axiom support means
  expressions like `ForAll(lambda k: Implies(k >= 0, fib(k+2) == fib(k+1) + fib(k)))`
  parse natively.

New benchmark `benchmarks/fib.py` synthesizes iterative Fibonacci.  The
invariant `a == fib(i) ∧ b == fib(i+1) ∧ 0 <= i ∧ i <= n` is recovered
from atomic predicates; the recurrence is supplied as a universally-
quantified axiom over the uninterpreted symbol `fib`.

Also: `synth/solver.py` now uses a *separate* per-call verifier
timeout (capped at 10s) distinct from the outer search budget.  With
quantified axioms in play, individual SAT checks can stall — the cap
lets CEGIS reject slow candidates and move on rather than wedging.

**Encoding lesson banked from Phase 3.D:**

8. **Naive CEGIS is O(search-space) in the worst case.**  Each
   counter-example only rules out a single indicator assignment.
   Phase 3.D's Fibonacci with one distractor per non-τ hole (~128
   combinations) times out repeatedly; the minimal-atom set
   (one atom per non-τ hole, 2⁴ τ subsets) converges in seconds.
   The fix is PLDI'09's *attribute-class* blocking from the
   predicate-abstraction reduction — group similar counter-examples
   and block them together.  Plan §5.6 called for this in "Phase
   1.C"; it's load-bearing for realistic predicate spaces.

**Phase 3.X — Smarter CEGIS blocker: DONE (incremental, 2026-05-11).**
Two layered changes:

1. **AtomRef plumbing.**  Each `SafetyConstraint` now carries an
   `atom_refs: list[AtomRef]` recording every τ atom that appears in
   its body, tagged with its position (antecedent vs. consequent) and
   the underlying Z3 expression at the appropriate binding.  The
   constraint generator (`synth/constraints.py:tau_at`) appends to a
   per-constraint accumulator while assembling each body.

2. **Restricted-relevance blocker** (`synth/solver.py:_smart_blocker`).
   When the verifier finds a counter-example for a constraint, the
   blocker is restricted to indicators that *actually appear* in
   that constraint's body — collected by walking the Z3 expression
   once.  Other constraints' indicators stay free, ruling out a
   larger class of bad assignments than the global exact-assignment
   block.

What it *does* fix: blocks are tighter per iteration, and the scope
of "current configuration is bad" is no longer leaked into unrelated
indicators.

What it *doesn't* fix: the fundamental O(search-space) ceiling of
naive CEGIS.  Each iteration still only learns from one
counter-example, and similar counter-examples across iterations
aren't aggregated.  `fib.py` (the minimal-atom version) is still the
only Fibonacci variant we can finish in reasonable time; a
distractor-rich version still wedges.

A **first** attempt used a stronger but **unsound** blocker that
flagged any consequent-position τ atom that evaluated False at the
counter-example as a "culprit" and asserted `⋁_culprit ¬b_q`.  That
banned valid atoms (e.g. IntSqrt's `x >= (i-1)*(i-1)` is unsound
in isolation but valid in the published conjunction).  Reverted to
the restricted-relevance form above, which is sound.

**Encoding lesson banked from Phase 3.X:**

9. **Per-failure attribute-class learning needs full context.**
   "Atom q failed in this counter-example" does NOT imply "atom q
   is bad in every assignment" — adding more atoms to the antecedent
   can rescue it (conjunctive τ strengthening).  A sound smart blocker
   must keep at least the relevant indicators' joint state, or
   precompute valid attribute classes upfront (PLDI'09).  The
   restricted-relevance variant is sound but only marginally faster
   than exact-assignment; real speedup requires PLDI'09's offline
   reduction.

**Phase 3.X.2 — PLDI'09 attribute-class reduction: DONE (2026-05-11).**
`synth/solver.py` replaced wholesale.  No more CEGIS loop.  Pipeline:

1. Per safety constraint, collect indicators that occur in the body.
2. Group by hole (τ → all subsets, non-τ → single-hot pick).
3. Enumerate the Cartesian product, substitute Booleans into the body,
   conjoin with axioms, ask Z3 whether the negation is unsat.  Each
   valid combination becomes a literal-product *cube* over the
   relevant indicators.
4. Encode each constraint as a disjunction of its valid cubes.
   Combine with well-formedness (PbEq).
5. SAT-solve.  Every model is a valid synthesis solution *by
   construction* — no per-candidate verification needed.
6. Enumerate top-K by adding differ-by-one blockers between solves.

All 10 benchmarks pass under the new solver.  fib now returns 3
solutions in ~5 minutes where naive CEGIS wedged.  Acyclic benchmarks
(swap, strassen, sat_sub) remain instant.  Single-loop benchmarks
spend most time in the enumeration (intsqrt 7s, sumi 5s, mul 12s,
max_array 17s) because we now compute the full validity tableau
upfront rather than incrementally — strictly more Z3 calls than CEGIS
took on these well-shaped problems, but each call is fast and
bounded.

**Encoding lessons banked from Phase 3.X.2:**

10. **PLDI'09 reduction trades CEGIS-scaling for upfront enumeration
    cost.** The big win is replacing O(search-space) CEGIS iterations
    with a polynomial number of Z3 quantifier-free unsat checks.
    For non-axiom-heavy benchmarks each check is milliseconds, total
    is seconds.  For axiom-heavy benchmarks (Fibonacci's recurrence)
    each Z3 check still has to do E-matching on the universal axioms,
    so per-check cost is 100ms–10s; the *number* of checks is small
    but each is expensive.  Distractor-rich fib still wedges
    individual checks — the bottleneck has shifted from CEGIS
    iterations to axiom-instantiation time.  The next optimization
    is explicit triggers / better patterns on axioms (or
    monotonicity-aware enumeration so axiom-heavy subsets are checked
    fewer times).  Note `_PER_CHECK_TIMEOUT_MS = 10_000` in
    `solver.py` — checks that time out are conservatively treated
    as valid; this can mask refutations.  Toggle to debug.

**Phase 3.X.3 — Perf optimizations on the PLDI'09 reduction: DONE
(2026-05-11).**  Two changes:

1. **Auto-trigger inference** (`synth/expr.py:_auto_triggers`).  When
   parsing `ForAll(lambda k: body)`, walk the body once for UF
   applications containing `k`; pass them as `patterns=` to
   `z3.ForAll`.  For the fib recurrence the auto-detected pattern set
   is `[fib(Var(0)), fib(Var(0)+1), fib(Var(0)+2)]`.

2. **Solver push/pop reuse** (`synth/solver.py`).  One reusable
   verifier with all axioms pre-asserted; each attribute-class check
   does `push() / add(Not(concrete)) / check() / pop()` instead of
   building a fresh solver each time.

Speedups (3.X.2 → 3.X.3 wall-clock):
  intsqrt 7s → 2s, sumi 5s → 1s, mul 12s → 2s, max_array 17s → 7s.
  swap/strassen/abs/sat_sub: instant in both.  fib 303s → 301s
  (auto-triggers gave near-zero benefit here; Z3 was already finding
  similar patterns on its own — the bottleneck is per-check Z3
  quantifier work, not axiom-assertion overhead).

**Encoding lesson banked from Phase 3.X.3:**

11. **Push/pop is where the real win is for non-axiom benchmarks.**
    Re-creating Z3 solvers for ~hundreds of attribute-class checks
    spends a lot on solver setup and (relevant for non-axiom problems)
    initial simplification.  One verifier + push/pop drops the
    overhead to per-check Z3 work.  Auto-triggers on axioms are a
    smaller lever — Z3's default auto-pattern selection is decent
    when there's a single recurrence-shaped quantifier.  Real
    Fibonacci-class speedups would need monotonicity-aware
    enumeration (cut the number of checks) or better axiom shapes
    (e.g. lazy / triggered closed-form expansion).

**Phase 3.E — recursion via POPL'10 §5.3: DONE (initial cut, 2026-05-11).**

Implementation: an SB branch transition atom can now be a *recur*
atom of the shape

    {"_recur": True,
     "args": {procedure_input_name: expr_over_pre_state, …},
     "ret":  {var_name: expr_over_returned_outputs, …}}

`synth/constraints.py:_recur_body` encodes POPL'10's
`s_recur = s_args ∧ (Fpre(vin') ⇒ Fpost(vin', vout'')) ∧ s_ret`:

  - Fresh Z3 variables represent the call's inputs (`vin'`) and
    outputs (`vout''`); they get universally quantified at the outer
    `ForAll` along with `V`.
  - `s_args` constrains each `vin'` from the pre-state via the user's
    `args` atom.
  - The induction hypothesis (`Fpre ⇒ Fpost`) is asserted as a
    conjunct of the transition body — the synthesizer assumes the
    recursive call satisfies its spec.
  - `s_ret` constrains each output / local at the post-state via the
    user's `ret` atom.
  - Inputs are preserved at the call site.

The decoder (`synth/decode.py:_emit_recur`) inlines the identity case
(`var := synth(args);`) and falls back to a temp form for non-identity
`ret` transformations:

    (_r_result) := synth(n - 1);
    result := _r_result - 1;

Two new benchmarks pass: `benchmarks/rec_const.py` (`f(n)` returns 0
recursively; published + variant solutions found) and
`benchmarks/rec_neg.py` (`f(n) = -n` via recursion with non-identity
`ret`).  All 12 total benchmarks pass; failure-channel test passes.

**Encoding lesson banked from Phase 3.E:**

12. **Safety without ranking admits non-terminating recursion.**
    The encoding accepts solutions like `else: result := synth(n)`
    (no decrease in args) — the induction hypothesis is "if the call
    satisfies the spec, our body satisfies the spec", which holds
    vacuously when the call diverges.  Per-procedure ranking
    function (similar to per-loop) ruling `ϕ(args') < ϕ(current
    inputs)` is the standard fix, in line with POPL'10's loop
    treatment.  Fixed in Phase 3.E.2.

**Phase 3.E.2 — per-procedure ranking: DONE (2026-05-12).**

A new hole `phi@PROC` is allocated by `expand` whenever any user
atom contains `_recur`.  The user supplies single-hot candidate
ranking expressions over procedure inputs.  Two new safety
constraints get emitted:

  - **Bounded** (once globally): `Fpre ⇒ ϕ_proc(inputs) ≥ 0`.
  - **Decrease** (per SB-branch × per recur-atom): gated on the
    atom's indicator, `current_pre ∧ branch_guard ∧ b_recur ⇒
    ϕ_proc(inputs) > ϕ_proc(args_evaluated)`.

The decrease check inlines `args_evaluated[v] = parse_expr(args[v],
pre_binding)` — no fresh Z3 vars needed for the ranking obligation
itself (the recur transition body still uses fresh `vin'`/`vout''`
for the induction hypothesis).

Both `rec_const` and `rec_neg` now rule out the wrong recur atom
(`args: {n: n}` with no decrease).  The proof annotation includes
`ranking PROC: n`.

**Encoding lesson banked from Phase 3.E.2:**

13. **Single-hot attribute-class enumeration must include the
    "all in-body False" option.** When only a subset of a single-hot
    hole's indicators appear in a constraint's body, there are two
    semantic possibilities: one of the in-body indicators is True
    (others — including out-of-body — False), OR all in-body
    indicators are False (an out-of-body indicator is True under the
    global PbEq).  My first attempt at Phase 3.E.2 only enumerated
    the first case, missing the valid "this constraint is vacuously
    true because the relevant recur atom isn't selected" cases.
    Both `rec_const` and `rec_neg` UNSAT'd as a result.  Fix:
    enumerate `M+1` cases per single-hot hole (M in-body True, plus
    one all-False); the main SAT solver prunes globally-infeasible
    all-False cases via `PbEq`.

**Regression suite split (2026-05-12):**
  - `.venv/bin/python tests/regression.py` — quick suite (~22s,
    skips fib).
  - `--slow` flag adds fib (~5 min total).
  Skipping fib by default avoids waiting on its axiom-heavy
  attribute-class enumeration in every routine check.

**Phase 3.F — Recur top-level + arrays in recursion: DONE (initial
cut, 2026-05-12).**  Three changes:

1. **`Recur` top-level template node** is now handled by `expand`
   (allocates `s@R<id>` hole, atoms must be `_recur`-shaped) and the
   constraint walker (safety + per-atom decrease, just like an SB
   branch with a recur atom).
2. **Fixed `_recur_body` binding bugs** that bit when a variable is
   both input and output (e.g. an array `A` threaded through the
   procedure):
   - **Fpre vs Fpost bindings**: previously merged `args_z3` and
     `rets_z3` with rets overriding, breaking Fpre when it referenced
     an input-also-output var.  Now Fpre uses `args_z3` only; Fpost
     uses inputs from `args_z3` with outputs overridden by `rets_z3`.
   - **Preservation rule**: previously "always preserve inputs",
     which contradicted any `ret` assignment to a var that was both
     input and output.  Now: preserve any var NOT in `ret`.
3. **Enriched `ret` binding**: a `ret` expression's variable
   references resolve to the call's *returned* outputs (`rets_z3`)
   for output names and the procedure's *pre-state* values for
   everything else.  This lets `ret` do post-processing — e.g.
   `Update(A, n - 1, 0)` reads the returned `A` and uses the
   original `n` to compute the index.

**New benchmark** `benchmarks/rec_zero_array.py` — recursive
procedure zeroing the first n elements of an array.  Template is
just `Recur` (one rec call); the post-processing step `A[n-1] := 0`
is folded into the recur atom's `ret`.  POPL'10's vacuous-base-case
trick: at n = 0, the recursive call's args satisfy Fpre vacuously,
the IH is trivially true, and the procedure's own Post
(`∀k. 0 ≤ k < 0 ⇒ …`) is also vacuously true.  Synthesizer picks
the right atom, rules out wrong indices, no-op rets, and non-
decreasing args (via `phi@PROC`).  All 13 benchmarks pass.

**Encoding lessons banked from Phase 3.F:**

14. **`Recur >> SB` needs intermediate state binding.** My current
    constraint generator has a single `pre_binding` and `post_binding`
    that's shared across the whole template walk.  For
    `Recur >> SB`, the Recur's post is conceptually the SB's pre —
    but with shared bindings, that's a single Z3 state.  Two cleaner
    options for a future phase: (a) thread per-item (in_binding,
    out_binding) with chain links, or (b) compose item transitions
    symbolically (Recur's trans ∘ SB's trans as one Z3 expression
    with fresh intermediates).  For Phase 3.F MVP, I sidestepped by
    folding `Recur >> SB` into a single `Recur` whose `ret`
    expression does the post-processing — relies on `ret_binding`
    knowing about pre-state values, which is the third change above.

15. **Vacuous-base-case is what makes POPL'10's pure `~`-style
    templates work.** Programs without explicit conditional branches
    can still terminate correctly *if the spec is structurally
    vacuous at the base case* — sortedness on an empty subrange,
    zero-out on n=0 elements, etc.  General-purpose recursive
    procedures (factorial, decrement-chain) need conditional
    branches (Phase 3.E's `SB(n=2)` with a recur branch).  Both
    paths are now supported.

**Phase 3.G — intermediate state binding: DONE (2026-05-12).**

Restructured `synth/constraints.py:generate` around a per-checkpoint
state chain:

  - `states[0] = pre_binding`, `states[N] = post_binding`, intermediates
    fresh.  Item `k` operates from `states[k]` (its `in_b`) to
    `states[k+1]` (its `out_b`).
  - Items between checkpoints (loops or program boundaries) are
    *bundled* into a single safety constraint:
    `bundle_pre(state_start) ∧ ⋀_items trans(state_k, state_k+1)
     ⇒ target(state_end)`.
    The verifier picks intermediate state values when checking
    attribute-class validity — universal quantification is implicit
    via Z3's free-variable semantics.
  - Loops are checkpoints with their own constraints (body inductive,
    decrease, lower-bound) emitted using FRESH body bindings.
  - Per-Recur decrease constraints inside a bundle use the
    accumulated bundle antecedent (bundle_pre + preceding
    transitions in the chain), so the decrease is evaluated against
    state[k]'s actual content.

`benchmarks/rec_zero_array_chain.py` validates the chain: same
problem as `rec_zero_array` but expressed as `Recur >> SB`, with the
post-processing in a separate acyclic block instead of folded into
the recur's `ret`.  Synthesizer correctly emits

    A := synth(A, n - 1);
    A := Update(A, n - 1, 0);

— the POPL'10 `~;◦` shape.  All 14 benchmarks pass; quick suite
runs in ~17s.

**Known restriction**: bundled chains accept only SB(n=1) and Recur
items between checkpoints.  Multi-branch SB(n>1) in a chain isn't
supported yet (would require enumerating per-branch combinations
across all items in the bundle — a Cartesian blowup).  Top-level
SB(n>1) (no chain) is still handled by the original multi-branch
path-emission code.

**Phase 3.H — `~;~;◦` template validation: DONE (2026-05-12), but
real sorts deferred.**

`benchmarks/rec_zero_double.py` validates the POPL'10 MergeSort-
shaped template `Recur >> Recur >> SB` end-to-end:

    A := synth(A, n - 1);
    A := synth(A, n - 1);
    A := Update(A, n - 1, 0);

Both rec calls decrease `phi@PROC = n`; the SB's `Update(A, n-1, 0)`
completes the post.  The second rec call is technically redundant
for this spec — the point is structural: the bundled 3-item chain
emits a single safety constraint
`Fpre(s0) ∧ r1(s0,s1) ∧ r2(s1,s2) ∧ sb(s2,s3) ⇒ Fpost(s3)` plus
two per-Recur decrease constraints.  All 15 benchmarks pass.

**Real MergeSort / QuickSort is out of scope for this push.**  The
gap, in order of decreasing tractability:

1. **Multi-branch SB inside a chain.**  A real sort needs a
   conditional base case (`if hi - lo <= 1 do nothing; else
   recurse + merge`).  Phase 3.G's chain bundling only accepts
   SB(n=1) and Recur — multi-branch SB(n>1) in a chain would emit
   one safety constraint per Cartesian combination of branches
   across items.  Plausible refactor in the same shape as
   `branch_paths` (single-item) generalized to chains.

2. **Refined ranking for recursion at the base.**  POPL'10's
   `~;~;◦` MergeSort relies on the vacuous-Fpre trick at the base
   case (empty subrange) — but my decrease constraint
   `current_pre ∧ b_recur ⇒ ϕ(in) > ϕ(args)` fires even when the
   recursive call's `args` themselves violate Fpre (so the IH is
   vacuous).  Fix: weaken to `current_pre ∧ b_recur ∧ Fpre(args)
   ⇒ ϕ(in) > ϕ(args)` — decrease required only for "live" rec
   calls.

3. **High-level merge/partition atoms.**  POPL'10 §5.3 uses a
   restricted `Rcomp` (swap/move only).  For sort to be tractable
   in our framework, the user would either supply an abstract
   `merge(A, lo, mid, hi)` UF with appropriate sortedness axioms,
   or unroll merge as a nested loop (which itself isn't supported
   — `Loop(Loop(SB))` is rejected today).

**Encoding lesson banked from Phase 3.H:**

16. **`~;~;◦` works structurally; full sorts need three additional
    pieces.**  The bundle/chain encoding from 3.G handles the
    template shape, but POPL'10's actual sort benchmarks need
    (i) multi-branch SB-in-chain, (ii) ranking that respects
    vacuous-Fpre for "skipped" recursive calls, and (iii)
    high-level abstract atoms for the merge/partition step.  Each
    is independently load-bearing; deferred to Phase 3.I+.

**Phase 3.I — independent guards + multi-branch SB in chains:
DONE (2026-05-12).**  Three coordinated changes:

1. **Drop cumulative-else; independent guards per branch.**  SB(n=k)
   now allocates **n** explicit guard holes (was n-1).  `branch_paths`
   returns `(g_i, s_i)` pairs without conjoining `¬g_{<i}`.  Disjoint-
   ness isn't enforced (POPL'10 §3.4 explicitly notes this is OK);
   total coverage `⋁ g_i ≡ true` is asserted as a separate
   well-formedness obligation.

2. **Cartesian-path chain bundling.**  `chain_transitions` is gone;
   `chain_paths(start, end)` yields per-path `(guards, transes)`
   tuples via `itertools.product` over multi-branch SBs in the chain.
   Per-path safety: `bundle_pre ∧ ⋀ guards ∧ ⋀ transes ⇒ target`.
   Recur decrease constraints likewise iterate over upstream paths.

3. **Coverage constraints.**  For each multi-branch SB at chain
   index k, per upstream path: `upstream ⇒ ⋁ g_i(states[k])`.  Rules
   out partial programs where some inputs hit no branch.

**Decoder** renders `if (g_0) … else if (g_1) … else if (g_{n-1}) …`
with all n synthesized guards (no implicit "else").

**Updated benchmarks**: `abs`, `sat_sub`, `max_array`, `rec_const`,
`rec_neg` — each had to add the extra `g@B.*` candidate list.  New
benchmark `benchmarks/rec_zero_array_branched.py` validates SB(n=2)
*inside* a chain (`Recur >> SB(n=2)`), emitting:

    A := synth(A, n - 1);
    if (n > 0) { A := Update(A, n - 1, 0); }
    else if (n <= 0) { /* skip */ }

All 16 benchmarks pass; quick suite ~20s.

**Encoding lesson banked from Phase 3.I:**

17. **Per-path Cartesian enumeration is the right unit.** POPL'10's
    PathC is naturally per-control-flow-path; my Phase 2.5 cumulative-
    else implementation was a special case (enforced orthogonality at
    encoding time).  Generalising to multi-branch SBs in chains is
    just "enumerate Cartesian over branch choices across items in the
    bundle" — modular and matches POPL'10.  Coverage is a separate
    well-formedness check that prevents partial programs; without it
    the synthesizer can pick guards that leave some inputs uncovered
    (e.g. `abs` could pick `x < 0 / x > 0`, missing x == 0).  The
    Cartesian growth is real but moderated by the fact that
    predicate spaces (which the LLM eventually drives) stay small —
    a handful of guards per SB and a handful of items per chain.

**Phase 3.J — vacuous-Fpre ranking refinement: DONE (2026-05-12).**

Both decrease emitters now gate on `Fpre(args)`:

  - `_emit_recur_decreases_for_hole` (SB-branch recur atoms).
  - `_emit_chain_recur_decreases` (chain recur atoms).

Constraint shape:
    bundle_pre ∧ ⋀ path ∧ b_recur ∧ Fpre(args)
      ⇒ phi(in) > phi(args)

When the recursive call's args violate Fpre, the IH is vacuous and
no termination obligation is required.  This is POPL'10's vacuous-
base-case ranking pattern (MergeSort with empty subranges).

**Demonstration benchmark `benchmarks/rec_clamped_phi.py`** —
identical to `rec_zero_array` but the `phi@PROC` candidate list
contains only a *clamped* expression `n if n > 0 else 0`.  Without
Phase 3.J, the decrease at n = 0 would require `0 > 0` (since
clamped ϕ also returns 0 at n = -1), which fails — synth UNSAT.
With Phase 3.J, args.n = -1 violates Fpre, decrease is skipped, and
the clamped ϕ is accepted.  All 17 benchmarks pass; quick suite
~22s.

**Encoding lesson banked from Phase 3.J:**

18. **Vacuous-Fpre is the standard ranking dodge for "skipped"
    recursive calls.**  POPL'10 §5.3 implicitly assumes IH is
    irrelevant when Fpre(args) is false (no obligation generated).
    My initial Phase 3.E.2 ranking constraint missed this — it
    required strict decrease even when the IH was vacuous.  Phase
    3.J makes the constraint precise; the change is one extra
    conjunct (`Fpre(args)`) per decrease emission and unlocks
    ranking functions that are "monotonic where it matters" (e.g.
    clamped at the Fpre boundary).  This is the cleanest example
    so far of a sound but useless-without-refinement constraint
    becoming useful with one well-placed weakening.

**Phase 3.K — nested loops: DONE (2026-05-12).**

The Loop handler in `constraints.py` previously rejected any non-SB
body (`raise NotImplementedError`).  Phase 3.K lifts the restriction:
Loop bodies can be any Template (SB, Loop, Seq, Recur).  Implementation:

1. Items walk is factored into a `walk_template(template, pre_state,
   post_state, pre_fn, post_fn)` closure inside `generate()`.
2. The Loop handler keeps the SB-body fast path (per-branch inductive
   + decrease emitted directly).  For non-SB bodies, it recursively
   calls `walk_template` with fresh body bindings and a `post_fn` that
   conjoins τ_outer with the ϕ_outer-decrease obligation.
3. `chain_paths` now handles Loop items by emitting an abstract
   transition `τ_inner ∧ ¬g_inner ∧ frame_eqs` at the Loop's exit
   state.  `frame_eqs` preserve vars NOT in the Loop body's modified
   set, conservatively over-approximated by `_modified_vars_of_template`.
4. Bundles no longer reset across Loops — the bundle's antecedent
   spans the full chain.  This is essential: without it, the outer
   ranking decrease can't relate ϕ_outer(body_in) to ϕ_outer(body_out)
   across an inner Loop, because τ_inner alone doesn't constrain vars
   it doesn't touch.

**Demonstration benchmark `benchmarks/nested_loop.py`** — doubly-nested
counter `SB; Loop( SB; Loop(SB); SB )` proving `i == n`.  The inner
loop is a no-op (counts j from 0 to n) — purely there to exercise
the nested-Loop machinery.  Quick suite now 18 benchmarks (~42s).

**Encoding lesson banked from Phase 3.K:**

19. **Across abstract loop transitions, frame preservation must be
    asserted at the binding level via equations.**  Loop invariants
    are evaluated at a single binding, so τ_inner cannot express
    "i preserved from outer-body entry" — it has no name for that
    earlier state.  The fix: when a Loop appears in a chain, its
    abstract transition is `τ_inner(it_out) ∧ ¬g_inner(it_out) ∧ ⋀
    (it_out[v] == it_in[v]) for v ∉ modified_vars(body)`.  The
    modified set is a syntactic over-approximation: union of LHS
    vars across every transition atom of every block in the body
    (recursively into nested templates).  This is sound and tight
    enough to admit the published nested_loop solution.

**Phase 3.L — monotonicity-aware τ enumeration: DONE (2026-05-12).**

The PLDI'09 reduction enumerates 2^|atoms| subsets per τ hole per
safety constraint.  For many constraints, the τ atoms appear in a
single position — only-antecedent (LB, decrease, ranking, final post
bundles) or only-consequent (Loop-entry constraints).  In those
cases the validity is monotone:

  - **CONS-only** (atom only in consequent): validity is monotone-
    *downward* in the τ subset.  The hardest case is the full set;
    if it passes, every subset passes.
  - **ANT-only** (atom only in antecedent): validity is monotone-
    *upward*.  The hardest case is the empty set; if it passes,
    every subset passes (premise alone implies conclusion).
  - **BOTH** (e.g. inductive `τ ∧ g ∧ trans ⇒ τ'`): no monotonicity
    guarantee, enumerate as before.

Implementation in `synth/solver.py`:
  1. New helper `_classify_atoms(sc)` builds a per-`(hole, atom_idx)`
     position set from `sc.atom_refs` (existing infrastructure from
     Phase 3.X).
  2. New helper `_free_tau_position(hid, bs, classification)` returns
     the shared position for a τ hole if all in-body atoms agree, else
     None.
  3. Per constraint, τ holes split into `free_taus` (single-position)
     and `other_holes` (BOTH or non-τ).  We enumerate the Cartesian
     product over `other_holes` only.  For each combo, the free τ
     holes are first checked at their "hardest" assignment (full for
     CONS, empty for ANT) — if it passes, the emitted cube omits the
     free-τ literals entirely, leaving them unconstrained in the main
     SAT.  If the hardest fails, fall back to enumerating those
     holes' subsets.

Speedups (3.K → 3.L wall-clock):
  - **nested_loop**: 20.4s → 4.6s (~4.4×).  Per-constraint atom
    breakdown shows 4 of 7 τ-bearing constraints had all-free τ
    holes (enumeration collapses 8 or 256 combos to 1); one partial
    (256 → 8); only the inductive (BOTH) keeps its 32.
  - **max_array**: 8.0s → 8.0s (no change — its big constraints have
    τ in both positions).
  - Everything else: within noise; τ holes are small (3–5 atoms)
    so 2^n wasn't the bottleneck.

**Encoding lesson banked from Phase 3.L:**

20. **Per-position monotonicity collapses single-position τ
    enumeration to 1 check.**  Conjunctive τ has a clean lattice
    structure with directional monotonicity per atom position.
    Single-position holes (LB, decrease, entry, final bundles)
    benefit dramatically — the hardest case answers everything.
    The inductive constraint (`τ ∧ g ∧ trans ⇒ τ'`, both sides) is
    the holdout; with BOTH atoms, neither direction is monotone and
    full enumeration stays.  Total cost of the optimization: one
    extra Z3 check per `other_holes` combo (the hardest free-τ
    case), which pays for itself the first time it passes.

**Phase 3.M — nested loops with array writes: DONE (2026-05-12).**

`benchmarks/nested_zero_array.py` — triangular zero-fill exercising
Phase 3.K's frame preservation for arrays.  The outer body writes
`A[i] := 0` *before* the inner Loop runs; the inner Loop is a no-op
counter.  The inner's modified-vars set is `{j}`, so the abstract
Loop transition's frame eqs preserve `A`, `i`, `n` from inner entry
to inner exit — load-bearing for the outer body's final-bundle
proof (which derives the extended zero-prefix from
`A_body_out = Update(A_body_in, i_in, 0)` composed with outer τ's
prefix-zero atom at `body_in`).

Synthesized solution (0.2s):

    int i, j;
    i := 0;
    while (i < n)   // τ = (0 ≤ i) ∧ (i ≤ n) ∧ (n ≥ 0)
                    //     ∧ (∀p. 0 ≤ p < i ⇒ A[p] == 0),  ϕ = n - i
    {
        A, j := Update(A, i, 0), 0;
        while (j < i)   // τ = (j ≤ i) ∧ (n ≥ 0),  ϕ = i - j
        {
            j := j + 1;
        }
        i := i + 1;
    }

Note the solver picked a MORE minimal τ_inner than the human
witness — just `j ≤ i ∧ n ≥ 0`, dropping `0 ≤ j` and `i < n`.
Both are derivable from the antecedent path or unused at exit.

**Encoding lesson banked from Phase 3.M:**

21. **Inner-loop τ does NOT need array atoms when the inner Loop's
    body doesn't touch the array.**  First attempt at this
    benchmark put a quantified prefix-zero atom and `A[i] == 0` in
    `τ_inner` ("for symmetry" with outer τ).  Result: 7 atoms in
    `τ_inner`, 2^7 = 128 enumerated subsets on the inner inductive,
    each a Z3 quantifier-heavy check — Z3 hung past 7 minutes.
    Removing the array atoms (the inner body is just `j := j + 1`,
    so any array atom is preserved by the frame eq through the
    abstract transition anyway) dropped τ_inner to 4 atoms, 2^4 =
    16 subsets, total time 0.2s.

    The general rule: each τ atom should bear weight *somewhere*
    in the local proof obligations.  Adding "carry-over"
    preservation atoms is wasted enumeration when the frame eq
    already gives the binding-level equality.

**Regression-suite subprocess isolation: DONE (2026-05-15).**

`tests/regression.py` now invokes a per-benchmark subprocess
via `tests/_solve_one.py`.  Each benchmark gets a fresh Python
interpreter — Z3 state is no longer shared across runs.

Why: order-dependent Z3 state was leaking between benchmarks.
matrix_init went 6s standalone → 369s after grid_paths ran
first.  rec_const flaked between sound and unsound winners
depending on what preceded it (Phase 5.B encoding lesson #28).
For a soundness-oracle suite where solution-count drift is the
guard (Lesson #31, P1), reproducibility is non-negotiable.

Cost: ~1–2s per benchmark for Python startup.  Quick suite
total bumps from ~25s to ~50s.  Acceptable.

Verified reproducible: quick suite returns identical counts
forward and reverse order (27/27 both).

**Encoding lesson banked from this fix:**

40. **In-process synthesis runs are not reproducible.**  Z3
    accumulates state — random seeds, solver instances reused
    across check() calls, cached unsat cores.  Even when nothing
    in our code shares state explicitly, the Python process's
    Z3 environment does.  Order-dependent flakes are the
    symptom; subprocess isolation is the fix.  Apply this
    pattern to any test surface that uses solver state (regression
    suite done; emit_py/emit_c/emit_rust still pending if they
    show order flakes).  Cost is small; reproducibility is
    table-stakes.

**Ring 2 Day 11 — sound-by-default + potentially_unsound flag:
DONE (2026-05-16).**

Three pieces:

1. **Default mode is now sound.**  `Problem.potentially_unsound:
   bool = False` (previously: `verify_fallback: str = "accept"`
   which silently used the lenient fallback).  Sound mode means:
   the synthesizer only emits solutions whose obligations were
   ALL genuinely verified — either by Z3 or by the Lean backend
   (always tried when available).  When neither can decide,
   synthesis returns `NoSolution`.
2. **`--potentially-unsound` CLI flag** + `Problem.potentially_unsound
   = True` opt-in for the lenient fallback.  Use when external
   reasoning establishes obligations the backends can't dispatch.
3. **`SOUNDNESS.md`** (new, top-level): documents the policy
   semantics — what "verified" means, what the flag changes,
   how the runtime check + regression guards compensate.

**Day-10 correction.**  My earlier "Lean fallthrough solves fib /
sum_array" claim was overclaimed: with `verify_fallback="lean"`,
the LENIENT fallback was still active, and the per-class Lean
calls were silently erroring/UNKNOWN-ing without halting
synthesis.  The successes were 95% lenient-saved, 5% Lean-saved.

Day 11's strict mode exposes the truth: under sound default,
fib's tactic chain currently can't close any of its 13 axiom-
heavy classes (recurrence E-matching needs per-shape tactic
templates).  sum_array closes 2/7 but the remaining 5 aren't
covered.  Both opt into `potentially_unsound = True` as honest
acknowledgement of the tactic-chain gap.  Future Ring 2.X
work: per-shape templates for `recurrence-axiom + UF` patterns.

Other 28 quick-suite benchmarks (Z3-decidable + the lenient-not-
needed ones) pass under sound default.

**`emit_axiom_declarations` bug fixes (Day 11 found during the
sound-default switch):**

  - Function-type UF args now parenthesized in axiom signatures:
    `sum : (Int → Int) → Int → Int` (was `Int → Int → Int → Int`,
    silently mis-typed).
  - Axioms referencing free program variables (e.g., sum_array's
    `sum(A, 0) == 0` over input array `A`) are now wrapped in
    `∀ A : Int → Int, …` so they're well-formed at file scope.
    Previously the axiom was emitted with `A` unbound → Lean
    rejected.

Both bugs were masked at Day 10 by the lenient fallback (Lean
errored on every call, but the lenient promotion accepted
anyway).  Sound-by-default surfaced them.

`SolveResult.hints` propagates Lean-dispatch telemetry on
success path.

12/12 Lean backend tests green; 28/28 quick regression green.

**Encoding lesson banked from Day 11:**

44. **Lenient fallback masks translator bugs.**  Day 10's
    `verify_fallback="lean"` was supposed to demonstrate Lean's
    capability.  But because the lenient fallback was still
    active, every Lean failure (whether due to a tactic-chain
    gap OR a translation bug in `emit_axiom_declarations`) was
    silently accepted via lenient promotion.  Two real translator
    bugs (axiom-type parens, free-var quantification) only
    surfaced when sound-default forced honest verdict reporting.
    Lesson: if you advertise a soundness improvement, gate the
    lenient fallback off when testing it.  Otherwise the
    "improvement" is whatever fraction the new path actually
    closes, padded by lenient — invisible to the maintainer.

**Ring 2 Day 10 — capability demo + sum_array benchmark + tempfile
verify: DONE (2026-05-15).**

Three pieces:

1. **Capability demonstrated end-to-end.**  Two benchmarks now
   prove Lean fallthrough's value-add:

   | Benchmark   | reject (Z3 only)  | accept (lenient)  | lean (fallthrough) |
   | ---         | :-:               | :-:               | :-:                |
   | sum_array   | **FAIL** (17s)    | success (19s)     | **success (47s)**   |
   | fib (slow)  | **FAIL** (130s)   | success (130s)    | **success (180s)**  |

   `reject` is the new strict policy (no lenient promotion of
   UNKNOWN-deferred classes; deferred classes stay rejected).
   Z3 alone leaves 6 UNKNOWN classes on sum_array, 13 on fib.
   Lean fallthrough closes them.  This is the first time the
   synthesizer is SOUND-er than Z3 alone — solutions are
   genuinely verified rather than lenient-accepted.

2. **`benchmarks/sum_array.py` (new).**  Recursive UF
   (`sum : (Int → Int) → Int → Int`) with base `sum(A, 0) = 0`
   and recurrence `sum(A, k+1) = sum(A, k) + A[k]`.  τ uses
   `s == sum(A, i)` as the inductive invariant.  Z3 leaves 6
   UNKNOWN classes (axiom-heavy E-matching over UF + array
   read).  Lean's `nlinarith` + axiom-rewriting closes all 6.

   Added to quick regression (28 benchmarks total).  Synthesizes
   in ~20s under default `accept` policy.

3. **No more `lean/SynthLean/Generated.lean` churn.**  Previously
   every test/verify call wrote to that committed file, polluting
   `git status` and creating race conditions.  Now both
   `tests/test_lean_backend.py:_build_generated` and
   `synth.lean_backend.verify.verify_class_via_lean` use a
   per-call `tempfile.NamedTemporaryFile` + `lake env lean
   <tempfile>`.  Each call is ALSO faster (5-6s vs 9-10s) since
   `lake env lean` skips the project-wide dependency check that
   `lake build` does.

   `Generated.lean` deleted; `SynthLean.lean` no longer imports
   it.  Standalone `lake build` builds Basic + GridPaths only.

`verify_fallback` policy is now properly enforced for all three
values:
  - "accept" (default): lenient fallback on UNKNOWNs.
  - "lean": Lean fallthrough on UNKNOWNs (this push).
  - "reject": strict — UNKNOWNs stay rejected (this push).

`SolveResult.hints: list[str]` field added so success-path
telemetry (Lean dispatch counts) is observable.

12/12 Lean backend tests green; 28/28 quick regression green
under default policy.

**Ring 2 Day 9 — solver UNKNOWN-fallthrough: DONE (2026-05-15).**

`synth/solver.py:_on_unknown` now consults
`verify_class_via_lean` before deferring a Z3-UNKNOWN class —
gated on `Problem.verify_fallback == "lean"` AND `sc.kind in
_REJECT_UNKNOWN_KINDS` AND `lean_available()`.  If Lean
returns VALID, the class is recorded as valid (Z3 was the
limiting factor).  If Lean says UNKNOWN/ERROR, the existing
two-pass fallback (deferred → lenient retry) applies.

Two solver-internal helpers:
  - `_recover_chosen_atoms(problem, system, assign)` — reverse-
    maps the indicator-Boolean assignment to a chosen-atoms
    dict, filling in defaults for holes the assign doesn't
    touch.
  - `_extract_loop_id(sc)` — derives the loop_id from a
    SafetyConstraint's atom_refs (looks for `tau@<id>`
    references).

Telemetry: `lean_dispatch_hits/misses/errors` counters propagate
to `result.hints` so users can see how often the fallthrough
actually fired.

12/12 Lean backend tests green; 27/27 quick regression still
green under default policy (lean fallthrough is opt-in;
default `accept` preserves all prior behavior).

Day 10 next: write a new compressor-style benchmark (e.g.,
sum_array, factorial, or list_reverse) that exercises Lean's
strengths — recursive specs that SMT struggles with but Lean
dispatches naturally.

**Ring 2 Day 8 — LeanVerifier infrastructure: DONE (2026-05-15).**

`synth/lean_backend/verify.py:verify_class_via_lean(problem,
chosen_atoms, sc_kind, loop_id)` is the unit the solver's
UNKNOWN-fallthrough path will call (Day 9 work).  Translates the
chosen-atom subset into a Lean theorem via the existing
theorem_for_<kind> builders, writes to `Generated.lean`, runs
`lake build`, returns `Verdict(status, elapsed_s, detail)` with
status in `{"valid", "unknown", "error"}`.

`Problem.verify_fallback : str = "accept"` field added (`accept`
| `lean` | `reject`).  Default preserves current behavior;
opt-in for the Lean path.

11/11 Lean backend tests green.  Test
`test_verify_class_via_lean_sumi_ranking_lb` exercises the new
verify infrastructure end-to-end (~9s wall-clock, dominated by
mathlib import compile + omega; subsequent calls in the same
process would be ~3s incremental).

Day 9 = solver.py integration: when a per-class Z3 check returns
UNKNOWN and `verify_fallback == "lean"`, route to
`verify_class_via_lean`.

**Lean backend Ring 1 — COMPLETE (2026-05-15).** Days 1–7
landed.  Full review in `lean/RING1_REVIEW.md`.

Headline result: grid_paths's inner-loop inductive — the
obligation SMT wedged on past 10 min — proves in Lean in
3.2s with a hand-written 30-line proof (Day 5).  The
translator auto-emits the right shape + dispatches 8 of 9
conjuncts; the remaining one needs per-shape tactic
templates (Ring 2 work).

Ring 1 capability claim **validated**; Ring 2 go/no-go = **go**.

**Day 1** — `lean/` directory holds a Lake project (`SynthLean`
library) with a smoke test in `SynthLean/Basic.lean` covering
literal/tactic/quantified/conditional/array-store shapes.  Lean
toolchain pinned to `leanprover/lean4:stable` (resolves to
`v4.29.1`); elan auto-installs on first `lake build`.  Project
builds clean from scratch.  `./lean/setup.sh` is the idempotent
one-command setup.  CI integration via `leanprover/lean-action@v1`.

**Day 2** — `synth/lean_backend/translate.py` translates
IR-level synthesis obligations to Lean theorem text.  Translation
level: atom strings, NOT Z3 expressions.  This was a real
design decision (recorded as Lesson #39): the user pushed back
on Z3 → Lean translation, pointing out that by the time you're
at Z3 the IR structure (named atoms, kinds, holes) is gone.
Atom-string-level lets each chosen τ atom become a NAMED
hypothesis (`h_tau_0`, `h_tau_1`, ...) — Hoare-style readable
theorems rather than flat SMT conjunctions.

Coverage so far: `theorem_for_ranking_lb` — emits

    set_option linter.unusedVariables false in
    theorem L0_phi_lb
        (x i v : Int)
        (h_pre : x ≥ 1)
        (h_tau_0 : v = i*i)
        (h_tau_1 : x ≥ (i - 1)*(i - 1))
        (h_tau_2 : i ≥ 1) :
        x - (i - 1)*(i - 1) ≥ 0 := by omega

for intsqrt's loop ranking-LB obligation.  Lean's core `omega`
tactic dispatches both intsqrt's and sumi's ranking-LB (it
treats nonlinear products as opaque variables, which is exactly
what's needed for these shapes).

`tests/test_lean_backend.py` runs the full pipeline: synthesize
→ translate → write to `lean/SynthLean/Generated.lean` →
`lake build`.  3 tests pass (intsqrt, sumi, multiple-in-one-
build).  Generated.lean ships in git as a placeholder
(`namespace ... end namespace`) so standalone `lake build`
without the tests stays green; the test run overwrites it.

CI adds a `Lean backend tests` step after the existing
`Lean backend build` step.

**Encoding lessons banked from Day 2:**

39. **For backend ports, stay at the level of user-authored
    abstractions, not the SMT compilation thereof.**  My first
    instinct on the Lean backend was Z3 → Lean — translate the
    same expression Z3 sees.  User pushed back: Z3 is too low.
    By the time atoms are conjoined into one Implies, you've
    lost the named-hypothesis structure that makes Lean
    theorems readable.  The right level is the atom strings the
    user wrote (`"v == i*i"`, `"x >= (i-1)*(i-1)"`); each
    becomes a named hypothesis in the emitted theorem.  Cost:
    a separate Python → Lean string translator (~80 LOC,
    similar shape to `emit_rust._rs_expr`).  Benefit: theorems
    that a human can read AND that name proof obligations the
    same way the user named them.  This will compound when we
    add Ring 2's Verifier abstraction — being able to talk
    about `h_tau_3` instead of "literal 12 in the And" is
    load-bearing for any debug experience.

**Day 3** — `theorem_for_ranking_decrease` covers loops with
SB(n=1) bodies and parallel-dict transitions.  Pre-state and
post-state vars get separate binders (`x i`, then `x' i'`); the
transition contributes `h_trans_<var> : <var>' = <rhs>`
hypotheses; the conclusion is `phi(pre) > phi(post)` with
transitioned vars primed in phi.  omega handles sumi/mul/
array_zero (linear ranking-decreases).  4 new tests in
`tests/test_lean_backend.py` (total 7), all green.

Array encoding switched mid-Day-3 from `Nat → Int` to `Int →
Int`.  Program loop counters are `Int`; `store : (Nat → Int)
→ Nat → ...` required `.toNat` coercions at every call site
involving a program variable.  `Int → Int` matches the SMT
encoding exactly and keeps `0 ≤ k` antecedents in user
invariants meaningful (vs trivially-true over Nat).  Updated
`SynthLean/Basic.lean` `store` def, `lean_expr` ForAll/Exists
emission, and `_state_binders` array typing.

**Day 4** — mathlib wired in (`require mathlib from git
"https://github.com/leanprover-community/mathlib4.git" @ "master"`
in `lean/lakefile.lean`; `import Mathlib.Tactic` in
`SynthLean/Basic.lean`).  `lake update` pulled 8419 pre-built
mathlib oleans via lake-cache — first build ~12s, subsequent
incremental builds ~3s.  `theorem_for_safety_inductive` lands.
Tactic chain:

    subst_eqs
    refine ⟨?_, ?_, …⟩          -- one ?_ per τ atom
    all_goals first | omega | nlinarith

`subst_eqs` substitutes each `h_trans_<var> : <var>' = <rhs>`
into the goal; the conjunction is split; each sub-goal is
dispatched by omega (linear) or nlinarith (nonlinear).
Discharges sumi's `2*s' = i'*(i'+1)` from `2*s = i*(i+1)` —
exactly the polynomial-expansion class that core Lean's omega
can't crack.  Also discharges mul's `p' = a*i'`.

Two new tests in `tests/test_lean_backend.py` (sumi, mul
inductive).  Total 9 Lean backend tests, all green.

**Day 5 — grid_paths inner inductive proves in Lean.** Ring
1's capability claim is validated.  `lean/SynthLean/GridPaths.lean`
hand-writes the obligation that the SMT path wedged on past
10 minutes (documented edge-of-feasibility benchmark).  Lean
compiles the proof in **3.2s**.

Foundation work (also Day 5):
  - `store2d : (Int → Int → Int) → Int → Int → Int → Int → Int → Int`
    added to `SynthLean/Basic.lean` — the 2D-array Store
    equivalent for `int[][]` benchmarks.
  - `paths : Int → Int → Int` declared as `axiom` (Lean's
    uninterpreted-function shape).  The three recurrence/base
    axioms emitted as `axiom paths_base_row`, `paths_base_col`,
    `paths_rec` declarations.

The proof structure:
  1. `subst h_trans_L h_trans_j` — eliminate the primed-var
     transition hypotheses.
  2. `refine ⟨h_tau_0, h_tau_1, ?_, ?_, h_tau_4, h_tau_5, ?_, ?_, ?_⟩`
     — bookkeeping conjuncts dispatched by direct hypothesis
     application; quantified conjuncts left as goals.
  3. The "current row up to column j' = j+1" conjunct does
     case-on-`q = j`:
       - `q = j` case (the just-updated cell): rewrite via
         `if_pos`, apply the recurrence axiom `paths_rec` and
         the prior τ atoms.
       - `q ≠ j` case: rewrite via `if_neg`, apply h_tau_7.
  4. The column-0-preserved conjunct uses `if_neg` (since
     `j ≥ 1`, position `(p, 0)` is never the updated cell).

What this validates:
  - 2D array Stores compose cleanly with `paths`-style UF
    axioms in Lean — no quantifier-instantiation wall.
  - The mathlib `paths_rec`-style axiom is directly usable as
    a rewrite rule; Lean's term unification handles what Z3's
    E-matching couldn't.
  - The proof is human-readable, named-hypothesis structured,
    and ~30 lines including comments.

What remains for Day 6+:
  - **Translator emission of this theorem.**  Right now it's
    hand-written; the translator needs to support nested loops
    (`Seq` body of `Loop`) and emit axiom declarations from
    `Problem.axioms`.
  - **Outer inductive.**  grid_paths's outer loop has body
    `SB >> Loop >> SB` (Seq); the inner loop's abstract
    transition + frame eqs need translation.

**Encoding lesson banked from Day 5:**

41. **Hand-writing the target proof first is the right Day-5
    move.**  Generalizing the translator to emit a class of
    proofs is much easier when you've already proven one
    instance.  Iterating tactics in a hand-written setting
    surfaced the right structural moves (`subst h_trans_*`;
    `refine ⟨…⟩` for the conjunction; `by_cases` on the
    quantified index against the updated cell; `if_pos`/
    `if_neg` for the store2d expansion).  Each of these maps
    cleanly to a translator template, so Day 6 is "automate
    the proof I wrote" rather than "discover how to prove
    this".  Demonstrates Ring 1's capability before paying for
    Ring 2's general dispatch.

**Day 7 — tactic engineering + end-of-Ring-1 review.**

Tactic-chain improvements (`synth/lean_backend/translate.py`):
  - `(aesop; done)` gating — fixes the "aesop partial
    progress shadows fallback" issue.  Without `done`,
    aesop's leftover state blocks the subsequent `simp_all`
    branch.
  - `split_ifs` fallback after `simp_all [store, store2d]`
    — handles if-conditions left by store-unfolding.
  - `solve_by_elim` fallback — applies hypotheses recursively.

After improvements, the translator closes 8/9 conjuncts of
grid_paths inner inductive.  The 9th (current-row case 2 or
column-0, depending on tactic ordering) needs `apply h_tau_X;
omega` — pick the matching pre-state hypothesis and discharge
its side condition via omega.  This pattern is generic to
"obligation involves array read at a position the loop
invariant ranges over" — Ring 2 work for per-shape templates.

`lean/RING1_REVIEW.md` writes up the full Ring 1 result:
capability proof ✓, integration shape ✓ (with one Seq-body
restriction), tactic coverage table, go/no-go recommendation.

**Encoding lesson banked from Day 7:**

43. **`first | aesop | fallback` shadows the fallback when
    aesop makes partial progress.**  Lean's `first` doesn't
    revert non-progressing tactics — once aesop has made ANY
    move (even an intros), the goal state changes and
    subsequent fallback branches start from that altered
    state.  Wrap in `(aesop; done)` to require closure;
    otherwise the partial-progress trap costs hours to debug.
    General rule: any tactic that you intend as a "tries to
    close" should be gated with `done` in a `first` chain.

**Day 6 — translator automation foundation.**  Three pieces
landed in `synth/lean_backend/translate.py`:

  1. **2D array support** in `_state_binders` (`int[][]` →
     `Int → Int → Int` for both pre- and post-state binders)
     and in `lean_expr` (4-arg `Update(A, i, j, v)` →
     `store2d A i j v`).
  2. **Axiom emission** via `emit_axiom_declarations(problem)`
     — translates `Problem.uninterpreted` to Lean `axiom`
     declarations and `Problem.axioms` to `axiom user_axiom_<k>`
     declarations.  The test harness prepends the axiom block
     at file scope (before the namespace).
  3. **Beefier generic tactic chain** in `theorem_for_safety_
     inductive`:
       `first | assumption | omega | nlinarith | aesop |
       (intros; simp_all [store, store2d]; first | omega |
        nlinarith | aesop)`
     `assumption` dispatches unchanged-from-pre conjuncts,
     `aesop` (mathlib general proof search) substitutes
     relevant hypotheses, and the `simp_all` fallback unfolds
     array-Store definitions.

The translator now emits the right SHAPE for grid_paths inner
inductive — axioms + binders + hypotheses match Day 5's hand-
written theorem in `SynthLean/GridPaths.lean`.  10 tests in
`tests/test_lean_backend.py` (9 build-and-prove from Days 2–4
plus 1 text-emission check for grid_paths) all green.

**What Day 6 didn't finish.**  The generic tactic chain
discharges all the conjuncts EXCEPT one in grid_paths: the
column-0-preservation conjunct (`∀ p. 0 ≤ p ≤ m → L' p 0 = 1`).
After `subst_eqs` and aesop, the residual goal is

    store2d L i j (...) p 0 = 1

which Day 5's hand-written proof closes with `rw [if_neg
(by omega)]; exact h_tau_8 p ⟨left, right⟩`.  Generalizing
that case-on-the-updated-cell pattern across benchmarks is
Day 7's tactic-engineering work.  For now the test only checks
emission correctness; the proof of grid_paths_inner_inductive
lives in the hand-written `SynthLean/GridPaths.lean`.

**Encoding lesson banked from Day 6:**

42. **Generic tactic search has a ceiling.**  aesop (mathlib's
    general proof search) gets you ~80% of the way on
    grid_paths-style obligations — substitutes relevant
    hypotheses, normalizes simp lemmas — but doesn't autonomously
    do the case-on-the-updated-cell move that array-Store
    inductives require.  The pattern needs explicit
    `by_cases` + `if_pos`/`if_neg` + named-hypothesis
    application, which is hard to generalize without per-
    obligation knowledge.  The right next move (Day 7+) is a
    library of obligation-shape-specific tactic templates
    rather than relying on aesop to discover them at proof
    time.

Per the scoping doc `RESEARCH.LEAN.md` Ring 1 plan.  Day 7 =
tactic-template library for array-modifying obligations +
end-of-Ring-1 review.

**P1 — solution-count regression as soundness oracle: DONE
(2026-05-15).**

`Problem.expected_solutions: int | None = None` is a new optional
field.  When set, the regression suite compares
`len(result.solutions)` against it and fails on mismatch with a
clearly-labelled `SOLUTION-COUNT MISMATCH` message.  When unset,
the check is skipped (incremental rollout for new benchmarks).

All 28 existing benchmarks (27 quick + 2 slow — fib +
selection_sort — minus 1 dup = 28) annotated with current
counts.  Mismatch path verified via fault injection (set
intsqrt's expected to 99; regression reports FAIL).

Why this matters: Lesson #31 documents that solution-count drift
was the signal that exposed the Phase 5.B++ generator-exhaustion
soundness bug (rec_zero_array went 1 → 3 solutions, including
unsound ones with non-decreasing recur args).  P1 promotes this
from "maintainer notices the number" to "CI fails the build".
Future refactors that accidentally drop a constraint from one
emission context (the Lesson #27 / #29 / #30 pattern) will be
caught automatically.

Promoted from `research.claude.md` P1.

**Encoding lesson banked from P1:**

38. **Solution-count drift is a free soundness signal — make it
    explicit.**  Pre-P1, the regression's solution-count column
    was informational only.  Now it's a hard guard.  Cost: ~30
    one-liner edits across benchmark files.  Benefit: any future
    refactor that widens the solution set (by accidentally
    dropping a constraint) fails CI immediately, before a
    runtime check would have to catch it.  The asymmetry
    (legitimate count *increases* should be rare — they usually
    indicate that an old constraint was over-restrictive, which
    is a knowledge step you'd update the annotation for anyway)
    favours strict equality.  False positives from this guard
    will be rare and informative.

**Phase 5.D — Rust emitter: DONE (2026-05-14).**

`synth/emit_rust.py` ships a Solution + Problem → Rust function
translator analogous to `emit_c.py`.  Differences from C:

- **Types.** `int` → `i64`; `int[]` input-only → `&[i64]`; `int[]`
  in-place (input+output) → `&mut [i64]`; `int[]` output-only →
  `&mut [i64]` (caller allocates).
- **Multi-output via tuple return.** No C-style out-pointers —
  Rust's tuple return handles multi-int outputs natively (e.g.,
  `intdiv` returns `(i64, i64)`).
- **Int inputs that are ALSO outputs** get `mut` on the parameter
  binding so the body can assign to them.  Returned by value at
  the end (Rust passes i64 by value, so the caller's copy isn't
  mutated).
- **Index casts.** Slice indexing requires `usize`; every array
  access is wrapped with `as usize`.  Done via AST rewrite so it
  composes through subexpressions: `A[j-1]` becomes `A[(j - 1) as
  usize]`.  Order matters: cast subscripts BEFORE substituting
  `and`/`or`/`not` (the substituted operators are invalid Python,
  so AST parsing has to run first).
- **`#[allow(non_snake_case, ...)]`** at the function level so
  user variable names (`A`, `X`, `Y`) don't trigger Rust lints.
- **2D arrays deferred** (same restriction as C emitter).

**Tests**: `tests/test_emit_rust.py` covers 11 benchmarks
(intsqrt, sumi, intdiv, abs, swap, array_zero, bubble_sort,
insertion_sort, rec_const, rec_neg, rec_zero_array).  Each
synthesizes + emits Rust + wraps in driver + `rustc -O` + runs
+ asserts stdout.  15s runtime timeout per binary to guard
against unsoundness producing infinite-loops.

**CI**: `.github/workflows/ci.yml` adds a `rustc --version`
toolchain check and a final "Rust emitter tests (compile + run)"
step.  ubuntu-latest comes with rustup pre-installed; no extra
install action needed.

**Encoding lessons banked from Phase 5.D:**

36. **Order matters when post-processing Python → another
    language.**  My first cut substituted `and` → `&&` before
    running the AST-based subscript-cast rewrite.  The
    intermediate string was no longer valid Python, so
    `ast.parse` errored, and `_cast_subscripts` silently returned
    the input unchanged — every `A[i]` access shipped without the
    `as usize` cast.  Rust rejected.  Fix: do AST rewrites FIRST
    (while it's still valid Python), then textual substitutions.
    The lesson generalizes: stack transpilation passes from
    "more-structured" to "less-structured" — AST-based passes
    have to run before regex passes.

37. **Rust's `mut` on parameters is a separate concern from
    `&mut` borrows.**  An `i64` parameter that the function body
    writes to needs `mut` on the binding, even though i64 is by
    value.  Easy miss because the same variable in C just works
    (C parameters are always mutable locals).  The fix is one
    line in signature emission: int inputs that are also outputs
    get the `mut` prefix.

**Phase 3.S — `int[][]` framework extension + 2D-DP exploration:
DONE (2026-05-14).**

**Framework extension.**  `synth/constraints.py:_type_sort` and
`_make_z3_var` learn `"int[][]"` → `z3.ArraySort(Int,
ArraySort(Int, Int))`.  `synth/expr.py:Update` becomes 3-or-4-arg:
3-arg is the existing 1D `Store`, 4-arg is the new 2D pattern
`Store(A, i, Store(Select(A, i), j, v))`.  Nested `A[i][j]` reads
work for free via the existing Subscript path (each Subscript
emits a `Select`, naturally chaining).  `synth/emit_py.py` learns
`int[][]` → `list[list[int]]`; `_emit_update_chain` decodes 2D
Updates to `A[i][j] = v`.  `synth/emit_c.py` raises a clean
NotImplementedError for `int[][]` (deferred — 2D C codegen needs
a width-aware shape).  All 26 prior quick-suite benchmarks still
pass.

**Why the extension was needed.**  First attempt at 2D DP
benchmarks (LCS, matrix_init) used 1D-flattening with index
arithmetic `i*n+j`.  Z3 wedged on quantified nonlinear arithmetic:
proving `∀p,q. A[p*n+q] == A[i*n+j]` requires reasoning about
`(p-i)*n+(q-j) = 0`, which Z3's quantifier-instantiation
heuristics couldn't crack in 5 minutes.  Native 2D sidesteps it
— `Select(Select(A, i), j)` is a pure array operation, no
multiplication of bound variables.

**matrix_init benchmark.**  `benchmarks/matrix_init.py` — zero-
fill an m × n 2D matrix.  First 2D benchmark to land.  Synthesis
in 6.1s with native 2D; the 1D-flattened version timed out at
5 min.  Added to the quick suite (27 benchmarks).  Python emitter
runtime-check tests `tests/test_emit_py.py:test_matrix_init_*`
exercise `Update(A, i, j, 0)` → `A[i][j] = 0` end-to-end.

**LCS + grid_paths — known timeout (research data points).**
Two further 2D-DP benchmarks are in `benchmarks/lcs.py` and
`benchmarks/grid_paths.py`.  Both wedge at 10–20 min synthesis
time.  Both are documented in their file headers as "known
timeout", NOT in the regression suite.  The wedge is the same
bottleneck class as fib (axiom-heavy: each per-class Z3 check
takes seconds because the validity question involves universal
axiom instantiation), but compounded by:
  - 2D array Stores inside the universal invariants
  - More atoms in τ_inner (~9) → 2^9 = 512 per-constraint subsets
  - Multiple constraints (entry, inductive, decrease, final
    bundle) each with axiom-heavy validity
grid_paths is the cleaner data point because it has NO case-
split in the recurrence (single equation `f(i,j) = f(i-1,j) +
f(i,j-1)`); its timeout shows the wedge isn't LCS-specific.
The 2D-DP-with-UF class is at the current edge of feasibility.

**Encoding lessons banked from Phase 3.S:**

34. **2D arrays as a native IR type beat 1D-flattening for
    quantified invariants.**  The arithmetic encoding of 1D-
    flattening (`A[p*n+q]`) puts a polynomial in array-index
    position, and quantified nonlinear integer arithmetic over
    such indices is at the edge of Z3's quantifier-instantiation
    capability.  Native 2D (`A[p][q]` as nested array reads)
    sidesteps it entirely.  For matrix_init the speedup was
    >50× (5+ min timeout → 6.1s).  The cost: one type to plumb
    through the IR, parser, constraint generator, and emitters
    — ~150 LOC across 4 files.  Worth it.

35. **Axiom-heavy benchmarks are bottlenecked at the per-class
    validity check, not the enumeration count.**  fib's 130s
    splits roughly evenly across ~hundreds of subsets, each ~1s
    of E-matching on its recurrence axiom.  LCS / grid_paths
    have 5–10× more subsets AND axioms that are heavier (UF
    application inside universally-quantified array reads), so
    per-check cost climbs to seconds, total wedges past 10
    minutes.  The fix isn't more τ-atom pruning (Phase 3.L
    already handles that); it's reducing the *per-check* axiom
    work — explicit triggers on the UF (some help, was already
    in 3.X.3), monotonicity-aware UF-axiom dispatch (would need
    new infrastructure), or a different backend for the
    recurrence portion (Lean tactic-based proof — `RESEARCH.md`
    §B).

**Phase 3.R — insertion sort: DONE (2026-05-14).**

`benchmarks/insertion_sort.py` — classical insertion sort with the
same sortedness-only post as bubble + selection sort.  Inner loop
walks the inserting element leftward by swapping with the "wall"
A[j-1], stopping at `j = 0 ∨ A[j-1] ≤ A[j]`.  Synthesized in 3.7s
standalone — added to quick suite (26 benchmarks now).

τ_inner has three quantified atoms (all picked by Z3):
  - **Left portion sorted**: A[0..j) sorted.
  - **Right portion sorted**: A[j..i] sorted (inserting element at
    j plus shifted-right slice).
  - **Wall lower-bound**: A[j-1] ≤ A[k] for k ∈ (j, i] when j > 0.

The wall-LB atom is what makes the inductive step go through: it's
the dual of bubble sort's "A[k] ≤ A[j] for k ≤ j" bubble property.
Both encode a physical fact (an array element bounds a slice) that
isn't derivable from sortedness alone.  The synthesizer picks all
three with no redundancy — score reflects that none can be dropped.

Both emitter test surfaces (`tests/test_emit_py.py`,
`tests/test_emit_c.py`) include insertion_sort with the standard
{5,3,8,1,9,2,7} input; Python runtime-check mode self-validates the
quantified invariants at every iteration in 15s.

**CI workflow: DONE (2026-05-14).**

`.github/workflows/ci.yml` lands.  Single job on ubuntu-latest +
Python 3.12; runs the quick regression, `proof_runtime` unit
tests, C emitter compile-and-run tests, and Python emitter
exec-and-runtime-check tests on every push to main and every PR.
pip cache, 30-minute timeout, LFS skipped at checkout (the `ref/`
PDFs / DLLs aren't needed by tests; saves bandwidth).
Concurrency group cancels in-progress runs of the same branch +
event when a new push lands.

Badge in README.md.

Per encoding lesson #32: the runtime-check emitter on every PR
gives us a real soundness guarantee, not just a syntactic
regression check.  If a future refactor reintroduces a Z3
UNKNOWN-conservative-accept gap or a constraint-emission scatter
(Lessons #26 / #27 / #30), the Python emitter's `proof_decrease`
or `proof_invariant` calls catch it before merge.

**Phase 5.C — Python emitter: DONE (2026-05-14).**

`synth/emit_py.py` ships a Solution + Problem → Python function
translator analogous to `emit_c.py`.  Two modes:

  - **Default** (`runtime_check=False`): proof annotations as Python
    comments, body is plain Python.  Idiomatic where Python differs
    from C: tuple-assignment for swap atoms (`x, y = y, x`), `A[i] =
    v` for `Update`, multi-int return as tuple.
  - **`runtime_check=True`**: lower proof obligations into calls
    against `synth.proof_runtime` — `proof_pre`, `proof_post`,
    `proof_invariant`, `proof_decrease`, `proof_lower_bound`,
    `proof_coverage`.  Quantified atoms (`ForAll`/`Exists`) are
    translated into `all(...)`/`any(...)` comprehensions using
    over-iteration with the original antecedent as a filter
    (always-correct fallback, simpler than per-variable range
    extraction).  Untranslatable atoms degrade to a `# runtime
    check skipped` comment.

Also handles two minor surface things:
  - `true` / `false` (lowercase, SMT-LIB style) → `True` / `False`.
  - All int outputs returned (Python passes ints by value), so
    `swap(x, y, c1, c2)` correctly returns a `tuple[int, int]`
    even when `x`/`y` are both inputs and outputs.

Tests: 14 cases in `tests/test_emit_py.py` (synth → emit → `exec`
→ call → assert), pairing every benchmark in both modes.  Pre /
post / invariant / decrease / coverage runtime checks all
verified to fire correctly on Pre violations.

**Soundness gap surfaced via Phase 5.C (banked, fixed in 5.C.2):**

`test_max_array_runtime_check` flaked under suite-load Z3
nondeterminism because the synthesizer occasionally picked `phi=i`
(one of three candidates including the correct `n - i`) as the
loop ranking.  `phi=i` is INCREASING, not decreasing, so the
emitted Python's `proof_decrease(i_out, i_in)` fired immediately.
Z3 should have rejected `phi=i` via the decrease constraint, but
it returned `UNKNOWN` on the per-class SAT check under quantifier
load (the τ_outer atoms include a `ForAll`), and the old solver
treated UNKNOWN as conservative-VALID (lesson #10).  Fixed in
Phase 5.C.2 below (lesson #33).

**Phase 5.C.2 — UNKNOWN-as-REJECT with two-pass fallback: DONE
(2026-05-14).**

`synth/solver.py:_REJECT_UNKNOWN_KINDS` lists constraint kinds
whose UNKNOWN validity check is treated as REJECT rather than
ACCEPT: `safety`, `coverage`, `ranking-decrease`, `ranking-lb`,
`ranking-proc-decrease`, `ranking-proc-lb` — every soundness-
carrying kind currently emitted.  Two-level fallback to keep
axiom-heavy benchmarks (fib) working:

  (a) **Per-constraint**: if strict-REJECT leaves a constraint
      with zero confirmed-valid classes, promote its deferred
      UNKNOWNs in-place.
  (b) **Global**: if the strict-pass main-SAT returns UNSAT,
      rebuild clauses with all deferred classes promoted and
      retry.  Axiom-heavy benchmarks (fib) land here — their
      right answers are among the UNKNOWN-deferred classes that
      Z3 couldn't prove in budget.

`test_max_array_runtime_check` is back online as a soundness
regression guard.  All 27 benchmarks pass (slow suite).  Failure-
channel + emit_py + proof_runtime suites all green.

**Encoding lesson banked from Phase 5.C.2:**

33. **Per-constraint UNKNOWN-REJECT alone isn't enough for
    axiom-heavy benchmarks; you need a global fallback.**  Fib's
    quantified-axiom safety checks are split across many classes
    — Z3 happens to prove a few (returns unsat), is uncertain on
    the rest (returns unknown).  A per-constraint fallback only
    triggers when every class is unknown, so it doesn't help when
    SOME classes confirm valid but they're not the right answer.
    The global fallback (retry the main SAT with all deferred
    classes promoted) catches this without giving up the
    soundness signal for max_array-style benchmarks where strict-
    REJECT lands on the right answer immediately.  Asymmetry of
    costs: false-positive (accept invalid) → unsound emitted
    code, runtime check catches it; false-negative (reject valid)
    → user supplies another atom set.  Strict-first / lenient-
    fallback gets you the best of both.

**Encoding lesson banked (#32):**

32. **The runtime-check emitter is a soundness oracle.** Phase 5.C's
    `runtime_check=True` mode caught a synthesizer soundness gap
    (Z3 UNKNOWN → conservative-accept on ranking-decrease)
    immediately the first time it ran on max_array under suite
    load.  The bug had been present since the lesson-#10
    conservatism was added; nothing prior tested whether the
    chosen `phi` actually satisfies its decrease property at
    runtime.  Worth thinking of compile-and-run-with-self-checks
    as a *required* test surface for any new constraint kind,
    not an optional one — every claim the synthesizer makes
    should be exercisable by emission + execution.

**Phase 5.B++ — full Loop/Recur emission centralization: DONE (2026-05-14).**

Followed up the SB centralization with the rest of Lesson #29's
cleanup.  Every well-formedness, coverage, ranking-decrease, and
ranking-LB constraint that applies to an IR construct now lives in
one named closure inside `walk_template`:

  - `emit_recur_decrease(hole_id, atoms, in_b, paths, branch_guard)`
    — per-procedure decrease, shared by SB-branch recurs and Recur
    items.
  - `emit_sb_constraints(sb, in_b, paths)` — SB coverage +
    delegates per-branch recur decrease to `emit_recur_decrease`.
  - `emit_loop_entry(item, in_b, idx)` — `bundle ⇒ τ(in_b)`.
  - `fresh_loop_body_bindings(lid)` — body_in/body_out allocation.
  - `emit_loop_body(item, body_in, body_out)` — body inductive +
    Loop decrease; dispatches SB-fast-path vs recursive walk.
  - `emit_loop_lb(item, body_in)` — `τ ⇒ ϕ ≥ 0`.

The Loop case in `walk_template`'s items loop is now a 4-line
dispatch.  The Recur case in the end-of-walk loop is a 5-line call
to `emit_recur_decrease`.  All three module-level
`_emit_recur_decreases*`, `_emit_chain_recur_decreases` helpers are
gone.

**Soundness fix #3 — generator exhaustion in emit_recur_decrease:
DONE (2026-05-14).**

The centralization itself surfaced a bug: `paths_to_in_b` is
typically passed as a generator (`_paths_to_state(k)`), and the
inner per-atom loop iterated it once per atom.  After the first
atom, the generator was exhausted, so atoms 1+ had NO decrease
constraint emitted.  `rec_zero_array` (4 candidate atoms,
including a non-decreasing degenerate at index 3) suddenly
returned 3 solutions including unsound ones.

Fix: materialize `paths_list = list(paths_to_in_b)` at the top of
`emit_recur_decrease` before the per-atom loop.  Trivial change,
caught by the regression's *solution-count* check: rec_zero_array
went from 1 → 3 solutions on the centralization, which only made
sense if soundness regressed.  The regression suite implicitly
guards against this via the solution-count expectation in CLAUDE.md
history.

**Encoding lessons banked (#30, #31):**

30. **Materialize generators at the function entry if any inner
    loop iterates them.**  Python's lazy generators are
    convenient but error-prone in nested-loop contexts: an
    exhausted generator silently produces zero items, which often
    looks like "no constraints needed here" — but in a soundness
    setting it means "constraint never asserted".  The fix is one
    line; the impact is correctness.  Apply this universally to
    helper functions that take iterables.

31. **Solution-count regression checks are a free soundness
    proxy.**  Pre-centralization rec_zero_array returned exactly 1
    sound solution.  Post-centralization (before the generator
    fix) it returned 3 — two of them with non-decreasing `args` and
    constant `phi@PROC`.  The "you suddenly get MORE solutions"
    signal jumped out of the regression output without any
    explicit assertion.  Worth keeping an eye on for future
    refactors.

**Array_zero "slowdown" investigation: not a regression.**  The
earlier 23.8s figure was CPU contention from stale
infinite-looping max_array binaries that had accumulated during
the emitter-test debugging.  Standalone timing now: 1.4s,
better than the pre-refactor 2.6s baseline.  Regression timing
fluctuates between 4.8s and 12.8s depending on what ran before it,
which is normal for shared-machine timing noise.

**Phase 5.B+ — SB-constraint centralization: DONE (2026-05-14).**

Following Lesson #27's identification of the "constraint X emitted
at one SB context but not another" pattern as bug-prone, did the
structural refactor.

Two new cover benchmarks targeting the bug class:
  - `benchmarks/cover_loop_branched_recur.py` — `Loop(SB(n=2))`
    with one branch being a `_recur` atom that has a non-decreasing
    degenerate alternative.  Exposed the SB-body-of-Loop fast path
    missing per-procedure-decrease emission (synthesizer picked the
    degenerate `args: {n: n}` solution; compiled C would
    stack-overflow).
  - `benchmarks/cover_chain_branched_recur.py` — `Recur() >> SB(n=2)`
    with branched recur.  Regression guard for today's chain-SB-
    decrease fix.  Already correctly rejects the degenerate.

Structural refactor: extracted `emit_sb_constraints(sb, in_b,
paths_to_in_b)` as a closure inside `walk_template` that emits ALL
context-applicable constraints for an SB:
  - Coverage `path ⇒ ⋁ g_i(in_b)` per path, if `sb.n > 1`.
  - Per-procedure decrease per (branch with `_recur` atom × path),
    gated on the branch guard, the atom indicator, and `Fpre(args)`.

Every SB-processing site now invokes this one function:
  - Chain walk (end of `walk_template` items loop) — uses
    `_paths_to_state(k)` which enumerates Cartesian paths through
    `chain_paths_local(0, k)`.
  - SB-body fast path of Loop — uses the single path
    `[τ_outer(body_in), g_outer(body_in)]`.
  - Future contexts (nested templates via recursive `walk_template`)
    inherit correct emission via their own end-of-walk loop calling
    the same helper.

`_emit_chain_recur_decreases` simplified back to Recur-item-only —
the SB-branch case I'd added earlier today is now subsumed by
`emit_sb_constraints`.

Also fixed an edge case in `solver.py` — when the Phase 3.L fast
path leaves `assign = {}` (every relevant indicator was in a free-
τ hole and the hardest case validated), the constraint's clause
should be universally valid; skip the clause emission rather than
crashing on `literals[0]`.

All 25 benchmarks (23 quick + 2 cover) pass.  All 10 emitter tests
pass.  array_zero got slower (4.8s → 23.8s) — noise or extra
per-SB enumeration work from the central helper; worth profiling
if it stays.

**Encoding lesson banked (#29):**

29. **Centralize constraint emission per IR construct.**  Every
    well-formedness / ranking-decrease / coverage constraint that
    applies to a multi-branch SB lives in one function; every
    site that processes an SB calls it.  Adding a new SB-related
    constraint kind is a one-place change; missing the constraint
    in one of N contexts is structurally impossible.  This kills
    the Lesson #27 bug class.  The same pattern should apply to
    Loop (LB + decrease + body-inductive), Recur (Fpre⇒Fpost +
    decrease + ret-binding), and any future IR construct.  Currently
    only SB is centralized; Loop and Recur are still partially
    scattered — future cleanup.

**Phase 5.B — C emission for Recur procedures: DONE (2026-05-14).**

Extended `synth/emit_c.py` to handle `_recur` atoms.  Three output
shapes supported:

  - Single int return: `result = fname(args);` for identity ret;
    `int _r_result = fname(args); result = <ret(_r_result)>;` for
    transform.
  - Array in-place (output also an input): `fname(args);` then apply
    any ret transformations via the standard assignment emitter
    (handles Update chains for the post-call writes).
  - Mixed: TODO comment.

Each recursive call site is wrapped in `if (<Fpre@args>) { ... }`
where Fpre is the procedure's precondition with input names
substituted by the call's args.  Without this wrap, pure
`~`-style templates (top-level `Recur()`, no explicit base case)
infinite-recurse at runtime — the synthesizer's vacuous-Fpre trick
proves correctness when the IH fires only on Fpre-satisfying args,
but a raw recursive C call has no analogous gate.

Three new tests in `tests/test_emit_c.py`: `test_rec_const`,
`test_rec_neg`, `test_rec_zero_array`.  All pass `clang -Wall
-Werror` compile + runtime check.  Total emitter test suite: 10
benchmarks, ~40s.

Also added a 15s runtime timeout in `_emit_and_check`: if a
compiled binary infinite-loops, the test now fails fast with a
diagnostic rather than hanging forever.  Earlier in the day I'd
lost ~30 min to stale infinite-looping binaries from before the
coverage fix piling up.

**Soundness fix #2 — decrease for SB-branch recur atoms: DONE
(2026-05-14).**

Same class of bug as the coverage fix from yesterday.  Surfaced via
test_emit_c's recur tests being flaky — running them AFTER
test_bubble_sort caused Z3 to pick a different (degenerate)
`result.best` for rec_const: `args: {n: n}` (non-decreasing!) with
`phi@PROC: 1`.  This should have been rejected by the per-procedure
decrease constraint `phi(in) > phi(args)`, but the constraint
**was never emitted for SB-branch recur atoms** — only for top-level
`Recur` items in the chain bundle.

Fix: extend `_emit_chain_recur_decreases` in `constraints.py` to
also iterate SB items, and for each branch with a `_recur` atom,
emit a decrease constraint gated on the branch's guard (the
existing SB shim was dead code — it had a callable form but no
caller).

The flakiness pattern is worth noting: **Z3 nondeterminism after a
heavy synthesis run can pick lower-score-but-soundness-buggy
solutions when constraints are missing.**  rec_const had been
returning the "right" solution by luck; bubble_sort's heavy run
shifted the solver state enough to flip preference.  Other recur
benchmarks were similarly vulnerable but happened to pick sound
solutions consistently.

**Encoding lessons banked (#27, #28):**

27. **Every well-formedness constraint that applies to a multi-
    branch SB must be emitted wherever that SB lives, not just at
    the top of the walk.**  This is the same lesson as #26
    (coverage) but for per-procedure ranking decrease.  An SB
    inside a chain bundle and an SB at the top of the walk look
    syntactically identical but get DIFFERENT constraint sets
    emitted.  Future similar bugs are likely lurking — the symptom
    pattern is "degenerate solution preferred by score, Z3
    nondeterminism reveals it under load".  When adding new
    constraint kinds, walk every SB-bearing context.

28. **Add a runtime timeout to compile-and-run tests.**  Synthesizer
    bugs can produce unsound code that compiles cleanly but
    infinite-loops at runtime.  Without a timeout, the test hangs,
    which masks the diagnostic value and burns CPU.  15s is plenty
    for our benchmarks; anything that takes longer is a bug.

**Soundness fix — coverage for SB-in-Loop-body: DONE (2026-05-13).**

Surfaced while validating the Phase 5.A C emitter: max_array's
synthesized solution #0 had branch guards `A[i] < m` and `A[i] <= m`
— which don't cover `A[i] > m`.  The emitted C falls through the
if/else chain when neither guard fires, and the outer loop's body
never advances `i`, causing the compiled binary to infinite-loop at
runtime on any input where the max is at some index > 0.

The root cause was in `constraints.py`'s walk_template: the SB-body
fast path (Loop with a single-SB body) emitted per-branch inductive
+ decrease constraints but NEVER emitted the coverage constraint
`τ_outer ∧ g_outer ⇒ ⋁ g_branch`.  Coverage was only emitted for
SBs in the *items* list of a walk (top-level template), not for SBs
that were the body of a Loop checkpoint.

The fix is one block in the fast path: when `item.body.n > 1`, emit
a coverage constraint scoped to the body's bindings.  All other
benchmarks have branch guards that happen to be tautological
(`x < 0 / x >= 0` for abs, `A[j] > A[j+1] / A[j] <= A[j+1]` for
bubble sort, etc.), so they were unaffected.  The bug only bit
benchmarks with NON-tautological guards.

**Cost**: regression's slower paths got slower — max_array 8 → 24s,
nested_loop 4.6 → 14.4s, bresenham_full 4.5 → 12.6s.  Worth it for
soundness.

`test_max_array` is re-added to `tests/test_emit_c.py` with input
`A = {3, 1, 4, 1, 5}` (all-positive, where every sound solution
converges to 5).  Catching this regression in the emitter test is
the intent: the emitter is the "ground truth" — if it produces a
binary that doesn't terminate or produces a wrong answer, the
synthesizer is the suspect.

**Encoding lesson banked (#26):**

26. **Coverage `⋁ g_i ≡ true` must be emitted wherever a multi-
    branch SB lives, not just at the top of the walk.**  This was
    a latent soundness bug in the SB-body-of-Loop fast path that
    existed for many phases but went unnoticed because every prior
    benchmark with an SB-in-Loop happened to have tautological
    guards.  The C emitter's runtime check (compile + execute on
    sample inputs) was the first artifact concrete enough to
    expose it.  Lesson: at every checkpoint where the synthesizer
    walks a multi-branch SB, ALL well-formedness constraints
    (coverage, single-hot, etc.) must be emitted with bindings
    scoped to that SB's evaluation context.

**Phase 5.A — C source emitter (initial cut): DONE (2026-05-13).**

`synth/emit_c.py` — Solution + Problem → compilable C function text.
First piece of Phase 5 (source emitters per plan.md).  Covers:

  - `int` and `int[]` (pointer-decayed) parameters and locals
  - while loops with proof-comment headers (invariant + ranking)
  - if / else-if / else-if chains for SB(n>1)
  - parallel assignment with temp-dance for true parallel semantics
    (so `{"x": "y", "y": "x"}` emits a swap, not `x = y; y = x;`)
  - SSA-list assignment (sequential)
  - array `Update` chain handling — single-write emits `A[i] = v`,
    nested (e.g. the bubble-sort swap idiom) captures all
    `A[expr]` reads into temps BEFORE any writes
  - pre/post in a header block comment
  - return-value vs out-pointer params: single non-input int output
    becomes the function's return; multi int outputs become
    `int *<name>_out` params with `*<name>_out = <name>;` writes at
    function exit

Not yet:

  - `Recur`: recursive procedure C emission needs its own design
    (procedure boundary, signature for the recursive callee, etc.).
  - Rust emitter — sibling of this, deferred.

Two compile-time concessions:

  1. Int locals are initialized to `0` at declaration.  Reason:
     clang's `-Wsometimes-uninitialized` can't see that the coverage
     constraint `⋁ g_i ≡ true` makes every code path assign them,
     so `int y; if (g0) y = ...; else if (g1) y = ...; return y;`
     triggers the warning.  Default-zero keeps the C valid under
     `-Werror`.
  2. Parallel scalar assignment with cross-references uses temps
     even when sequential emission would be correct (e.g. intsqrt's
     `v = v + 2*i + 1; i = i + 1;`).  Cheaper-than-analysis trade.

**Tests**: `tests/test_emit_c.py` synthesizes 6 benchmarks (intsqrt,
sumi, intdiv, abs, array_zero, bubble_sort), emits C, wraps each in
a `main()` driver, compiles with `clang -Wall -Werror`, runs the
binary, and asserts stdout matches the expected output.  All 6 pass
in ~30s total (bubble_sort dominates at 16s — most of it is the
synthesis step, not the emitter).

`test_max_array` was dropped from the suite: max_array's post is
underspecified (see problem.skill REC 5) so the synthesizer
returns multiple solutions including degenerate ones, and "which
solution does the emitter produce correct C for" is a synthesizer-
ranking question rather than an emitter-correctness question.

**Encoding lesson banked from Phase 5.A:**

25. **Coverage `⋁ g_i ≡ true` is a synthesizer guarantee that the
    target compiler doesn't see.**  Our SB(n>1) emission produces
    `if (g_0) ... else if (g_1) ... else if (g_{n-1}) ...` — every
    branch is a guard expression, even the last one.  Coverage is
    proved at synthesis time but clang's flow-analysis can't infer
    it, so any local assigned only inside the branches reads as
    "potentially uninitialized" downstream.  Two acceptable fixes:
    (a) default-initialize the local, (b) emit `else { ... }` for
    the last branch (semantically equivalent under coverage but
    drops the guard text from the code).  We picked (a) — keeps the
    proof annotation faithful to the synthesizer's structure.

**Phase 3.Q — selection sort: DONE (2026-05-13).**

Classic selection sort with the same sortedness-only post as bubble
sort.  Different inner-invariant shape: a min-index property
`∀k. i ≤ k < j ⇒ A[min_idx] ≤ A[k]`.  Synthesizer found the correct
solution in **312 seconds** standalone — added to the *slow* suite,
not quick.

The slowness vs bubble sort (6s) traces to **where the swap lives**:
- Bubble sort: swap is INSIDE the inner loop body.  The expensive
  Store-of-Store array reasoning happens inside the inner inductive,
  which is one constraint with τ_inner BOTH (2^6 = 64 subsets).
- Selection sort: swap is in the OUTER body AFTER the inner loop.
  The expensive Store-of-Store reasoning happens inside the outer
  body's final-bundle constraint, which must derive the extended
  sorted-prefix atom for the new `i = i + 1` using the swap's effect
  on A combined with the inner loop's exit-state min-index property.
  Each Z3 check on this constraint instantiates the quantified outer
  atom against the Store-of-Store, and the per-check cost dominates.

The synthesizer picked the minimal τ for both: dropping `0 ≤ i` from
the outer (not load-bearing — neither the post nor inductive
strictly need it) and `i < j` from the inner (subsumed by `min_idx <
j ∧ i ≤ min_idx` chain).

**Encoding lesson banked from Phase 3.Q:**

24. **Where the array-modifying transitions live matters more than
    how big τ is.**  Selection sort's τ_inner is the same size as
    bubble sort's (7 atoms vs 6), but selection sort is 50× slower.
    The difference is structural: bubble sort's expensive Z3 checks
    (array Store inside quantifier instantiation) happen inside one
    constraint with manageable atom count; selection sort's same
    expensive checks happen inside a constraint that also enumerates
    the outer τ.  When designing a template, prefer placing array-
    modifying transitions inside the smaller bundle.  Equivalently:
    moving the swap from outside to inside the inner loop (bubble-
    sort-style) trades 50× wall-clock for the same correctness.

**Phase 3.P — bubble sort: DONE (2026-05-13).**

The big one.  Optimized bubble sort with shrinking inner bound and
the full sortedness post — nested loops + quantified array
invariants on the inductive constraint, all in BOTH position.

    i := 0
    while (i < n):
        j := 0
        while (j < n - 1 - i):
            if (A[j] > A[j+1]):
                A := Update(Update(A, j, A[j+1]), j+1, A[j])
                j := j + 1
            else:
                j := j + 1
        i := i + 1
    // post: ∀p, q. 0 ≤ p ≤ q < n  ⇒  A[p] ≤ A[q]

Synthesized in **2.3s** standalone, 6.5s in regression.  τ:
  - Outer (4 atom candidates, 2 picked):
      i ≤ n  ∧  ∀p, q. 0 ≤ p ≤ q < n ∧ q ≥ n-i ⇒ A[p] ≤ A[q]
  - Inner (6 atom candidates, 5 picked):
      0 ≤ j  ∧  j ≤ n-1-i  ∧  i < n
        ∧  ∀p, q. (outer suffix-sortedness carried)
        ∧  ∀k. 0 ≤ k ≤ j ⇒ A[k] ≤ A[j]    (bubble property)

The bilateral atom `∀p, q. 0 ≤ p ≤ q < n ∧ q ≥ n-i ⇒ A[p] ≤ A[q]`
single-handedly captures both the suffix-sorted-ness (both p, q in
suffix) and the prefix-dominated-by-suffix (p in prefix, q in
suffix).  Cleaner than splitting into two atoms.

The inner inductive constraint enumerates 2^6 = 64 BOTH τ subsets;
each Z3 check has the conditional swap's Store-of-Store inside the
Forall body.  Z3 instantiates the universal patterns against the
Store structure via E-matching.  Per-check cost ~30ms — the whole
constraint clears in ~2s.  Phase 3.L's monotonicity fast path
handles every other constraint (entry, LB, decrease, coverage,
outer body's final bundle's τ_inner part — all single-position) in
single checks.

This validates the framework as a real proof-theoretic synthesizer:
nested loops + quantified array invariants + conditional swap
verified in seconds, on a tier-1 benchmark.

**Encoding lesson banked from Phase 3.P:**

23. **A single bilateral quantified atom can subsume what looks
    like two distinct invariants.**  For bubble sort the natural
    decomposition is "suffix sorted" + "prefix dominated by
    suffix".  Both are subsumed by ONE bilateral atom that
    quantifies p ≤ q and gates on `q ≥ n-i`: both-in-suffix gives
    sortedness, p-in-prefix-q-in-suffix gives dominance.  This is
    not just stylistic — fewer atoms mean a smaller 2^|atoms|
    enumeration on the BOTH inductive, and Z3 doesn't waste effort
    enumerating two-atom subsets that are redundant under
    conjunction.

**Phase 3.O — Bresenham's line drawing: DONE (2026-05-13).**

Two variants of the classical line-drawing algorithm with the
published bilinear algebraic invariant
`v == 2*dy*x - 2*dx*y - dx + 2*dy`:

  - `benchmarks/bresenham.py` (0.8s).  Post: `x == dx ∧ v ==
    2*dy*dx - 2*dx*y - dx + 2*dy` (loop terminates AND the algebraic
    invariant holds at exit).  Forces τ to carry the bilinear
    algebraic relation; simpler τ that ignores it can prove
    termination alone but not the algebraic post.

  - `benchmarks/bresenham_full.py` (4.5s).  Post: full quantified
    pixel-correctness
    `∀k. 0 ≤ k < dx ⇒ -dx ≤ 2·dy·k - 2·A[k]·dx ≤ dx`.  This is the
    classical POPL'10-era hard synthesis benchmark — Z3 must
    instantiate the quantifier against array Stores while
    discharging bilinear arithmetic.  τ has 7 atoms: algebraic,
    `x ≤ dx`, two `dx/dy >= 0`-flavored conjuncts preserved from
    Pre, `v ≤ 2·dy ∧ v ≥ 2·dy - 2·dx` (the v-range that combined
    with the algebraic invariant gives the just-plotted pixel's
    bound), and the quantified prefix atom carried across iters.

The full-post variant succeeding in seconds — not minutes — is a
real demonstration that the PLDI'09 reduction + Phase 3.L
monotonicity-aware enumeration + Phase 3.X.3 push/pop reuse compose
well even for bilinear-inside-quantifier validity checks.  The
inductive constraint has all 7 τ atoms in BOTH position so its
2^7 = 128 enumerated subsets run in full; the entry / LB / decrease
/ final-bundle constraints are single-position and short-circuit via
Phase 3.L's hardest-case fast path.

**Encoding lesson banked from Phase 3.O:**

22. **Force the algebraic invariant by putting it in the post.**
    A first cut with the trivial post `x == dx` synthesized
    Bresenham's correctly *but* picked the trivial τ `0 ≤ x ≤ dx`
    — the algebraic invariant wasn't load-bearing for any proof
    obligation, so PLDI'09 enumeration found minimal-atom subsets
    that satisfied everything.  Strengthening the post to include
    `v == 2*dy*dx - 2*dx*y - dx + 2*dy` made the algebraic atom
    necessary, restoring the "interesting" proof.  The general
    pattern: if you want a specific invariant to appear in the
    synthesized proof, the post or another constraint must require
    it.  Synthesis optimizes for score (atom count), not for what
    a human would write.

**Phase 3.N — integer division benchmark: DONE (2026-05-12).**

`benchmarks/intdiv.py` — repeated-subtraction division computing
`q, r` such that `x == q*y + r` and `0 ≤ r < y`.  Same bilinear-
invariant shape as `mul.py` but the inverse direction (mul builds
the product up, intdiv breaks the dividend down).  Two solutions
returned in 1.9s; the score-minimum drops the unused `q ≥ 0`
conjunct (monotonically increasing from 0, never required in any
proof obligation).

The benchmark serves as breadth, not depth — it adds a
classical-verification example without exercising new framework
features.  20/20 quick suite.

**Next (in order):**

1. **Insertion sort + DP benchmarks** (Checkerboard, LCS, possibly
   2D-as-1D matrix init).  Rounds out the sort family and starts
   DP-shape coverage.  Each is a stand-alone benchmark; no framework
   changes required.

2. **Phase 5.C — Python emitter** with an optional `runtime_check`
   flag.  Sibling of `emit_c.py` but the output is valid Python.
   The flag, when set, lowers proof obligations (pre / post /
   invariant / decrease / lower-bound / coverage) into calls to
   the `synth.proof_runtime` library — turning proof annotations
   from comments into executable runtime checks.

   The runtime check library (`synth/proof_runtime.py`,
   `tests/test_proof_runtime.py`) is **already built and tested**
   in preparation: `proof_pre`, `proof_post`, `proof_invariant`,
   `proof_decrease`, `proof_lower_bound`, `proof_coverage`, plus a
   generic `proof_check`.  Each raises `ProofViolation` (an
   `AssertionError` subclass) with structured diagnostics.  When
   the emitter lands, it just emits `proof_pre(<cond>, "<msg>")`
   etc. — no inline asserts.

3. **CI workflow — DONE.** `.github/workflows/ci.yml` runs the
   quick regression + `proof_runtime` + C emitter + Python emitter
   suites on push to main and on pull-requests.  Ubuntu-latest +
   Python 3.12; pip-cached; ~5–10 min total.  Cheap insurance: the
   soundness fixes from this session (#26, #27, #29, #30, #32)
   were the kind of regression a CI would have caught immediately.

4. **Phase 5.D — Rust emitter.** (Renamed from 5.C; Python takes
   that slot.)  Sibling of the C emitter; main novelty is borrowing
   semantics on the array out-parameter (`&mut [i32]` instead of
   `int *`).

5. **Phase 4 (PINS add-on) — DEFERRED, possibly replaced.**  The
   compressor/encoder benchmarks that PINS was originally for may
   instead motivate the Lean proof backend in `RESEARCH.md` §B.
   Held until we have empirical evidence one way or the other.

6. **C emitter for Loop+Recur composition** corner cases — Loop
   body containing a Recur, or Recur containing nested Loops.  The
   simple cases work but corners aren't validated.  Low priority
   until a benchmark needs it.
- Rust emitter — sibling of the C emitter.
  Each has a different inner-invariant shape — selection sort tracks
  a "minimum-index" pointer, insertion sort threads an element
  rightward.  Now that bubble sort works, these should be quick
  additions.
- Assume-guarantee sub-procedure abstraction (legitimate axiom-
  bearing path: contracts express genuine abstraction of helper
  functions, not a circular shortcut).  Now that a real sort works
  without it, this is justified only by *compositional* use cases
  — top-down decomposition where the LLM has guessed the sub-
  procedure's contract and the synthesizer verifies the outer
  program against it.
- Abstract merge/partition atoms with circular sortedness axioms:
  **off the table** — the axiom would state the answer.  Bubble
  sort just proved we don't need them.
- Source emitters (Phase 5 in plan.md): take the synthesized
  pseudo-code and emit real C or Rust.  Now that the synthesizer
  handles non-trivial algorithms, the next big mile is shipping
  the *code-and-proof* pair through to a target language.

