# COST_INVS — resource-bound invariants and the Lean-axiomatize approach

Design doc for extending the synthesizer with **resource-bound
invariants** (cost atoms in templates) so we can search for
algorithms by their asymptotic complexity, not just by their
correctness + termination.

This is **north star #1** ("from correctness to full resource
semantics", `README.md §North stars / DESIGN.md §0`) made concrete.
The motivating workload is L1.6 — "search for an algorithm beating
O(E + V log V) on interval bipartite matching" — but the
infrastructure applies to every benchmark.

The approach follows the framework's confirmed strength
(`CLAUDE.md` "Lean axiomatize + Z3 shim, NOT pure Z3 SAT search
past the wedge limit"): heavy structural reasoning lives in Lean
library theorems; Z3 threads a small parametric layer over the
top.

---

## 1.  Framing — what changes in the IR

Today every loop `Loop(...)` carries a `phi@*` ranking hole
(strictly decreases per iteration; ≥ 0).  This proves termination.

The extension: every loop **also** carries a `cost@*` hole — a
Real- or Int-valued expression in the loop's pre-state that
upper-bounds the cost of executing the loop.

```
Loop {
  τ@L  invariant atoms
  g@L  guard
  phi@L  ranking            ← already in IR
  cost@L cost atom          ← NEW
  body
}
```

Cost composes:
  - **Loop**: `cost(Loop) ≤ cost@L`, with the standard sum-over-
    iterations interpretation backed by a Lean lemma.
  - **Sequence**: `cost(S₁ >> S₂) = cost(S₁) + cost(S₂)`.
  - **Branch (SB)**: `cost(SB) ≤ max(cost branch_i)` (or +ε if we
    want tight expected cost; max suffices for worst-case).
  - **Recur**: `cost(Recur) ≤ cost@PROC` with recurrence T(n) =
    cost(body) + T(n-1) (or similar, handled by Lean cost lemmas).

The cost expression itself ranges over a candidate space supplied
by the user (similar to how `phi@*` ranges today).  Example
candidates: `n`, `n + m`, `n log n`, `n²`, `E + V`, `E + V log V`,
`E · √V`.

### Constraints emitted

For each loop with cost@L picked as `K(state)`:
  - **Bounded cost**: `K(pre_state) ≥ 0` (well-formedness).
  - **Cost decrement**: `cost_per_iter(state) ≤ K(state) -
    K(post_state)` — body's cost is paid for by the cost
    function's decrease.
  - **Cost-rank link**: typically `K = c · phi@L · per_iter_const`
    for simple linear-iteration loops; more complex recurrences
    handled by Lean lemmas.

These follow PLDI'09 §3 "Resource Templates"; we re-derive them
fresh per `DESIGN.md` "Locked decisions" — re-derive from PLDI'09, no
speculative refinements.

### Top-level proof obligation

For a `Problem` with `cost_target: str = "E + V"` (added field),
the synthesizer emits:

  `Pre ⇒ cost(entire template) ≤ cost_target(input)`

as a Z3 obligation.  The Lean backend dispatches axiom-heavy cases.

---

## 2.  Lean library — the load-bearing axioms

The framework's strength is Lean-axiomatized speculation.  For
resource-bounded search, the Lean library carries the heavy
structural reasoning.  Below is a minimum viable library for the
L1.6 interval-bipartite-matching target.

### Cost-composition lemmas (problem-independent)

```lean
-- General-purpose cost theorems used across benchmarks.
axiom LoopLinearCost :
    ∀ (n : ℕ) (body_cost : ℕ),
    body_cost ≤ K → cost (loop_n_times n body_cost) ≤ n * K

axiom SortCost :
    ∀ (n : ℕ),
    cost (sort n integers) ≤ n * log₂ n + C_sort
axiom RadixSortCost :
    ∀ (n : ℕ) (W : ℕ),  -- W bounds endpoint magnitudes
    cost (radix_sort n W) ≤ n * W + C_radix

axiom BFSCost :
    ∀ (V E : ℕ) (G : Graph),
    G.|V| = V → G.|E| = E → cost (bfs G) ≤ V + E + C_bfs
```

These compose: a template using `sort` + a `loop_n_times` body
yields total cost `O(n log n + iter_cost · n)`.

### Problem-specific predicates and theorems

```lean
-- Graph theory.
def Bipartite (G : Graph) : Prop := ...
def IntervalGraph (G : Graph) : Prop := ...
def Matching (G : Graph) (M : Set Edge) : Prop := ...
def MaxMatching (G : Graph) (M : Set Edge) : Prop := ...

-- Standard structural theorems.
theorem König : ∀ G, Bipartite G →
    |MaxMatching G| = |MinVertexCover G|
theorem IntervalGreedy : ∀ G, IntervalGraph G → Bipartite G →
    greedyMatch (sortedEndpoints G) = MaxMatching G

-- Known algorithm cost lemmas.
theorem HopcroftKarpCost : ∀ G, Bipartite G →
    cost (hopcroft_karp G) ≤ E · √V + C
theorem GloverIntervalCost : ∀ G, IntervalGraph G →
    cost (glover G) ≤ V * log₂ V + E + C
theorem BucketedIntervalCost : ∀ G, IntervalGraph G → BoundedEndpoints G →
    cost (bucketed_interval_match G) ≤ V + E + C
```

The last three lemmas are themselves *corpus benchmarks* — they're
verifiable Lean theorems about specific algorithms.  We would
prove them in the library as part of the infrastructure work.

### Composition theorems (the search target)

```lean
-- The search wants to instantiate templates whose composition
-- gives a cost bound.  Each composition is a Lean theorem.
theorem TemplateGloverShape : ∀ G,
    IntervalGraph G → Bipartite G →
    template = SB(sort_endpoints) >> Loop(sweep_step) →
    invariants_hold →
    cost ≤ V * log₂ V + E ∧ output = MaxMatching G

theorem TemplateBucketedShape : ∀ G,
    IntervalGraph G → BoundedEndpoints G → Bipartite G →
    template = SB(bucket_fill) >> Loop(scan_buckets) →
    invariants_hold →
    cost ≤ V + E ∧ output = MaxMatching G

theorem TemplateRadixSortShape : ∀ G,
    IntervalGraph G → BoundedEndpoints G → Bipartite G →
    template = SB(radix_sort) >> Loop(sweep_step) →
    invariants_hold →
    cost ≤ V + E ∧ output = MaxMatching G
```

Each composition theorem is what the Lean backend would CITE when
verifying a search candidate.  The Z3 search is over which
theorem to invoke — analogous to the L1.2 speculation framework
picking which `LIBRARY[entry]` to apply.

---

## 3.  The search space — template × invariants × cost atom

The framework's job: enumerate (template, invariant assignment,
cost atom) triples and use the Lean library to verify each.

### Template space (small finite enumeration)

For L1.6, an initial template set:

| ID  | Shape                                              | Expected cost | Status         |
| --- | ---                                                | ---           | ---            |
| T1  | `Sort >> Loop(sweep)`                              | V log V + E   | Glover         |
| T2  | `BucketFill >> Loop(scan)`                         | V + E         | Bucketed       |
| T3  | `Loop(adjacency_greedy)`                           | E             | Greedy (incorrect on general; correct on intervals if augmenting paths short) |
| T4  | `Loop(SB(layer_bfs) >> Loop(augment))`              | E · √V        | Hopcroft-Karp  |
| T5  | `RadixSort >> Loop(sweep)`                         | V + E         | Radix-sweep    |

Plus 1-3 speculative variants (e.g., dual-pointer sweep, prefix-
sum based, segment-tree augmented) — these are the "unknown
shapes" the search might rediscover or rule out.

### Invariant atom space (per template)

For each template, 4-10 candidate atoms.  Strassen-style: each
atom is a discrete predicate; Z3 picks subsets.

Example for T1 / T2:
```
"M is a matching on processed prefix"
"all endpoints with timestamp ≤ t are assigned-or-skipped"
"|M| equals greedy assignment count on processed prefix"
"unmatched interval count at time t ≤ width"
```

### Cost-atom space (per template)

Cost candidate is one of:
```
cost ≤ V
cost ≤ V + E
cost ≤ V · log₂ V + E
cost ≤ E · √V
cost ≤ V²
```

Z3 picks one cost candidate per template.  The Lean library
decides whether the picked cost is achievable for the template's
structure.

---

## 4.  Search mechanics — Lean axiomatize + Z3 shim

Per `(template T_i, invariant assignment I, cost candidate C)`
triple:

1. **Correctness obligation**: `Pre(G) ∧ Invariants(I) ∧
   template T_i applied to G ⇒ output = MaxMatching(G)`.  Dispatch
   via `verify_class_via_lean`; Lean library's `Template*Shape`
   theorems are the citation targets.
2. **Cost obligation**: `Pre(G) ⇒ cost(T_i) ≤ C(G)`.  Same
   dispatch shape; cost-composition lemmas + algorithm-specific
   cost theorems handle it.

Both must close for the triple to be valid.

### Search sweep direction

To **discover** sub-O(V log V + E):
  - Iterate C in INCREASING order: `V → V + E → V log V + E → ...`
  - First SAT pair `(T_i, I, C)` with C < V log V + E is a
    discovered algorithm shape with better cost.

To **rule out** sub-O(V log V + E):
  - Verify UNSAT for every C < V log V + E across every (T_i, I).
  - Result: "no template + invariant assignment in our library
    admits cost < V log V + E" — a Z3 + Lean-checked
    impossibility narrative for the enumerated shapes.

Same pattern as L1.2's S1-S6 sweep.

---

## 5.  Discovery vs. verification — what the deliverable looks like

### Pure-verification deliverable

For each named template (Glover, Hopcroft-Karp, Bucketed, etc.):
  - Lean-axiomatized correctness theorem.
  - Lean-axiomatized cost bound.
  - Corpus benchmark with `cost_target` field; synth solves it
    via cite to library theorem.

Outcome: a corpus of mechanically-verified bipartite-matching
algorithms with their cost bounds Lean-checked.

### Discovery deliverable

A `(template, invariants, cost)` triple found by the search where:
  - Template shape is **structurally distinct** from any in the
    initial library (e.g., a novel sweep variant).
  - Lean verification closes for both correctness and cost.
  - Cost beats the known bound.

Output: `(synthesized code, Lean proof, cost ≤ X)` — a
publishable algorithm + machine-verified proof.

### Negative-narrative deliverable

If discovery wedges (likely for genuinely-open frontiers):
  - The L1.2 / L1.5 narrative pattern: "across N enumerated
    templates and M invariant assignments per template, no
    instance admits cost < V + E."  Z3 + Lean-checked.
  - This is itself publishable as a structural lower bound on a
    well-defined class of algorithm shapes.

---

## 6.  Honest feasibility and ordering

### What's feasible after infrastructure work

| Feasible | Item                                                   | Effort       |
| ---      | ---                                                    | ---          |
| ✓        | Add `cost@*` holes to IR alongside `phi@*`             | 2-3 weeks    |
| ✓        | PLDI'09-style cost-decrement constraints               | 1 week       |
| ✓        | Lean cost-composition lemmas (general)                 | 1-2 weeks    |
| ✓        | Graph IR / UF axioms (adjacency UF, matching UF)       | 1-2 weeks    |
| ✓        | Lean library for bipartite matching + interval graphs  | 2-3 weeks    |
| ✓        | Glover / Hopcroft-Karp corpus benchmarks with cost     | 1-2 weeks    |
| ✓        | Template enumeration for L1.6 + L1.2-pattern sweep     | 1 week       |

Approximate total: **2-3 months** focused work to reach the
L1.6 search.  But this investment unlocks resource-bounded
versions of **every existing benchmark** + sets up other open
problems (L1.2 / L1.5 / L2.2 / L2.4 all become amenable to
cost-bound proof obligations).

### What's beyond reach

  - Amortized-cost reasoning (potential method; splay-tree style).
    Different formalism; would need additional infrastructure.
  - Data-structure inventions (e.g., Eppstein's path-graph
    technique) — the search space we enumerate is over
    control-flow templates with fixed primitive operations, not
    data structures.
  - Anything requiring nondeterministic / probabilistic cost.

### Recommended ordering

1. **Bootstrap (no L1.6 commitment)**: add `cost@*` hole +
   general cost-composition lemmas + cost-target field on
   `Problem`.  Verify existing corpus benchmarks at their natural
   cost bounds (e.g., sum_array at O(n), bubble_sort at O(n²),
   floyd_warshall at O(n³)).  This is north star #1 standalone
   and is independently valuable.
2. **Domain library**: graph IR + bipartite-matching axioms +
   interval-graph theorems.  Independent of cost layer; useful
   for L1.6 verification deliverables (Glover correctness alone).
3. **Composition**: combine 1 + 2 → cost-bounded matching corpus.
   Glover, Hopcroft-Karp, bucketed-interval as verified
   benchmarks.
4. **Search**: enumerate templates and run the speculation sweep
   per §4 above.  Discovery or impossibility narrative.

Steps 1-3 are corpus / framework expansion — each is independently
valuable.  Step 4 is the open-problem attack.

---

## 7.  Connection to other open problems

The cost-invariant infrastructure also enables:

  - **L1.2 / L1.5 / L2.1** revisited with **operation-count cost
    bounds** (each multiplication is cost 1; we already know the
    bilinear ranks; cost ≤ K formalizes the rank claim).
  - **L2.2** — sub-cubic min-plus matmul — directly a cost-bound
    search at 4×4 / 5×5.
  - **L2.4** — addition chains — each ADD is cost 1; chain
    length is the cost target.
  - **L3.x** — selection / merging / branchless networks: cost =
    SLP length, same shape as our current SLP work but now with
    cost atoms in the IR.

So the COST_INVS investment is foundational across the catalog,
not L1.6-specific.

---

## Status

- [x] **§1 IR extension — first slice DONE** (2026-05-21):
       - `cost_target: str | None` on Problem (default None).
       - `cost@<lid>` hole allocation in expand.py when
         cost_target is set; user supplies candidates via
         `atoms[f"cost@{lid}"]`.
       - Three new constraint kinds emitted in constraints.py:
         (A) cost-lb, (B) cost-decrement (body_cost = 1 for
         SB-body loops), (C) cost-budget at loop entry.
       - solver.py adds the three kinds to
         `_REJECT_UNKNOWN_KINDS` (soundness-critical).
       - decode.py prints `cost      L0: <expr>` in proof
         annotation parallel to `ranking`.
       - First end-to-end demonstration:
         `benchmarks/cost_invs/sumi_cost.py` — synthesizes
         in 0.1s, picks `cost@L0 = N - i` against `cost_target = "N"`.
         Negative test `sumi_cost_bad.py` correctly returns
         UNSAT when only invalid candidates supplied.
       - **First slice limits**: SB-bodied loops only (body_cost
         = 1).  Nested-loop and Recur cost-composition deferred
         to a later slice.  Scratch validation in
         `scratch/cost_invs_nested.py` confirms the math for
         O(n²) shapes; encoding extension is straightforward.

- [x] **§1.5 — nested-loop cost composition DONE** (2026-05-21).
       Implementation: `walk_template` gained an
       `enclosing_loop_id` parameter.  When set, after the
       per-construct step it emits a cost-decrement constraint
       per Cartesian path through the body chain, summing
       per-item body costs:
         SB           → 1
         Loop(inner)  → cost@L_inner(item_entry_state)
         Recur        → 0 (deferred to §1.6)

       `emit_loop_body`'s non-SB else branch passes
       `enclosing_loop_id=lid` to the recursive walk_template.

       First nested benchmark:
       `benchmarks/cost_invs/nested_cost.py` — doubly-nested
       counter with `cost_target = "n * (n + 2)"`.  Synthesized:
         cost  L0: (n - i) * (n + 2)   ← quadratic outer
         cost  L1: n - j               ← linear inner
       3 solutions (τ subset variations), all picking the
       published cost pair.

- [ ] §1 other follow-ups:
       Recur cost@PROC (analogous to phi@PROC);
       SB(n>1) per-branch cost variation (currently all
       branches assumed unit cost).
- [x] **§2 first slice — cost-composition lemma library**
       (2026-05-21).  Authored `lean/SynthLean/CostLemmas.lean`
       with 11 named lemmas covering linear cost identities,
       quadratic decrement step, nested-loop composition, and
       cost-budget closed forms.  All discharged via
       `ring` / `omega` / `nlinarith`.  Module compiles in
       5.4s as part of `lake build`.  Imported from
       `SynthLean.lean` root.

       Concrete next-up: a single cited lemma
       (`nested_loop_bubble_admissible`) directly proves the
       bubble_sort_cost cost-decrement — what currently pays
       Z3's 12× NIA tax could close in ms via Lean citation.

- [x] **§2 wiring (translators + UNKNOWN-fallthrough) DONE**
       (2026-05-21).  Three translators added in
       `synth/lean_backend/translate.py`:
       `theorem_for_cost_lb`, `theorem_for_cost_decrement`
       (SB-bodied), `theorem_for_cost_decrement_chain` (non-SB-
       bodied; uses `_chain_state_binders` + `_emit_chain_item_hyps`).
       Dispatch wired in `verify.py` (picks chain variant when
       outer Loop body is non-SB).  `cost-lb` and `cost-decrement`
       added to `_LEAN_TRANSLATABLE_KINDS` so `_on_unknown`
       routes them through Lean.  Tactic chain
       `omega | ring_nf+omega | nlinarith | linarith` with
       `open SynthLean.CostLemmas` for citation.

       Verified: existing cost benchmarks unchanged
       (sumi_cost, array_zero_cost still ~0.1s; sumi_cost_bad
       still UNSAT).

       **Speedup NOT delivered** on bubble_sort_cost.  Z3
       returns VALID (slowly, via NIA) rather than UNKNOWN,
       so Lean fallthrough doesn't fire.  An aggressive
       "always-route nested cost-decrement to Lean" gate was
       tried and reverted — per-subset Lean startup ×N
       subsets exceeded Z3's NIA total.  bubble_sort_cost
       stays at ~28s; this is acceptable as the scaffolding
       baseline.

- [ ] **§2 follow-up (deferred) — quadratic-routing heuristic**.
       To actually deliver the bubble_sort_cost speedup,
       inspect each `cost@L` atom for nonlinearity
       (multiplication of non-constant terms) and gate
       Lean-first dispatch on that signal.  Estimated
       ~1-2 hours of focused work.  Picks up when
       quadratic-cost benchmarks become a measured bottleneck.

- [x] **§3 — Graph + bipartite-matching Lean substrate DONE**
       (2026-05-22).  Three new modules under
       `lean/SynthLean/`:

       - `Graph.lean`: Adj, Undirected, Simple, Bipartite,
         IntervalGraph, BoundedEndpoints predicates; EdgeCount,
         Degree UFs with non-neg axioms.
       - `Matching.lean`: IsMatching, IsMaxMatching predicates;
         MatchingSize UF with non-neg + |M| ≤ N/2 bounds;
         Konig theorem (axiomatized); named-algorithm cost
         axioms HopcroftKarpCost / GloverIntervalCost /
         BucketedIntervalCost; ExistsMaxMatching; IntSqrt /
         IntLog2 Int-typed placeholders.
       - `MatchingSmoke.lean`: 3 composition theorems
         demonstrating clean citations + L16Target claim
         shape (the open question).

       All modules compile under full `lake build` (3-7s each).
       Pattern: follow L1.2/L1.5 — declare verified
       sub-algorithms + structural facts as Lean AXIOMS
       (trusted), search compositions with Z3 on top.
- [x] **§4 — L1.6 template speculation framework DONE**
       (2026-05-22).
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

       This is the framework-checked structural impossibility
       narrative for L1.6's open question — same L1.2-pattern
       shape but at the cost-bound level.  Lean closes each
       pair in ~4.5s.

- [x] **§5 — cost-bound on concrete operations DONE (2026-05-23).**
       `benchmarks/open_prbs/l16_bipartite_matching/bench_glover_concrete.py`
       synthesizes 1 verified solution in 441s with the same
       3-candidate exploration pool as Slice B.2 (full-pair /
       asymmetric / skip) PLUS `cost_target = "n"` and
       `cost@L0 = "n - i"`.

       **First benchmark to validate the cost-bound
       infrastructure on concrete-operations templates** —
       no UFs anywhere.  The three cost obligations
       (`cost-lb`, `cost-decrement`, `cost-budget`) all close
       via Z3-LIA dispatch.  Linear cost stays in the cheap
       regime; no NIA tax (lesson #56).

       The Tier-3 helper for the load-bearing sc2 cube
       (`sc2_fallthrough_fb5e83c0.solved.lean`) was ported from
       Slice B.2's `sc1_fallthrough_f16e259e` via a one-line
       sed rename — the only signature delta was the constraint
       INDEX (sc1 → sc2 because cost obligations sort before
       safety in `ConstraintSystem.safety`).  Same case-split
       + omega proof.

       **Why this validates §§1–4 cleanly**: §§1–4 designed and
       tested the cost-bound infrastructure on UF-axiomatized
       sub-algorithms (Slice A's `bench_glover_verify.py`).  §5
       proves the same constraint kinds compose with concrete
       state.  The framework dispatches cost obligations
       independently of whether the body's M-update is a UF
       application or a concrete `Update` expression — both
       reduce to the same `cost@L(in)` vs `cost@L(out)` check.

       Slice A → Slice B unification claim:
         Multi-candidate exploration + cost-bound discrimination
         works WITHOUT UF crutches.  Slice A's algorithm-picking
         mechanism (axiom-bearing → PICKED, no-axiom → rejected)
         transfers cleanly to concrete operations (preservation-
         provable → PICKED, can't-preserve → rejected).

       What §5 does NOT do: it doesn't introduce a new constraint
       kind, doesn't extend the IR, doesn't add helpers to the
       framework's tactic library.  It's a *validation* of the
       §§1–4 substrate on a new state class.

- [ ] Section 6 — bucketed-interval (sub-Glover) attempt.
- [ ] Section 7 — generalize to other catalog targets.

Cross-references:
  - `DESIGN.md §0`, `README.md §North stars` — north star #1.
  - `OPEN_PRBS.md L1.6` — the motivating open problem.
  - `CLAUDE.md` — Lean axiomatize + Z3 shim guiding principle.
  - PLDI'09 — resource templates reference.
