# Soundness of the synthesizer

This document describes what "synthesized code is verified correct"
actually means in this codebase.

## TL;DR

**The synthesizer is sound by default.**  Every solution returned
carries a proof — loop invariant, ranking function, transition
obligations — that was either decided by Z3 or proved by Lean
(generic mathlib tactic chain + curated `.solved.lean` companion
cache).  Synthesis returns `NoSolution` rather than emit
unverified code.

As of the chain-bundle Lean translator landing
(`theorem_for_entry_bundle` + `theorem_for_chain_bundle`), every
committed benchmark in the regression suite — including the
axiom-heavy ones (`fib`, `factorial`, `sum_array`,
`array_product`, `count_zeros`) — synthesizes under sound mode.

The earlier `--potentially-unsound` lenient fallback was excised
because no benchmark needs it.  The `Problem.potentially_unsound`
field remains as a development escape hatch (described below)
but its production code path is now dead.

## The validity check, in detail

The synthesizer reduces every safety obligation (loop invariant,
ranking-LB, ranking-decrease, chain-bundle entry, chain-bundle
post, coverage, …) to a per-attribute-class **validity check**.
For each (constraint, indicator assignment) pair we ask: *is
`body(this assignment)` valid for every program state V?*

Implementation: ask Z3 whether `Not(body)` is SAT.

- `unsat`   → no counterexample exists → **genuinely valid**.
- `sat`     → counterexample produced → **invalid**.
- `unknown` → Z3 ran out of time / heuristic budget.  No conclusion.

For axiom-heavy obligations (UF recurrences, quantified array
invariants), Z3's quantifier-instantiation heuristics often return
`unknown`, AND can sometimes return spurious `sat` or `unsat`
(by misinstantiating universally-quantified axioms).  Lean is the
arbiter for these cases.

## How undecided obligations are handled

The pipeline is layered:

1. **Z3** runs first for non-axiom-heavy problems.  For axiom-heavy
   problems + soundness-critical constraint kinds (see routing
   allowlist below), Z3 is bypassed entirely and Lean is consulted
   from the start.  See `_axiom_heavy_lean_path` in
   `synth/solver.py`.
2. **Tier-3 helper citation** (Phase H.2.CODEGEN, 2026-05-19).
   Before any cache lookup or generic tactic chain, the obligation
   is matched against the benchmark's `helper_registry` (if any).
   When a HelperEntry's `required_atoms` is a subset of the
   chosen-atom subset, the codegen module emits a one-line
   `exact <helper> <args>` proof referencing a hand-proven helper
   in `Helpers.lean`.  Cost: 2-5s (cached `.olean` + single-term
   type-check) vs 30-60s for the generic chain.  See
   `synth/lean_backend/codegen.py`.
3. **Lean cache check.**  When no helper applies, the curated
   companion cache is consulted:
   `<theorem_name>_<H>.solved.lean` → VALID; `.invalid.lean` →
   INVALID (definitive reject).  Signature hashes (`_signature_hash`)
   make this content-addressable.
4. **Lean generic tactic chain** (when the toolchain is available
   and no cache hit).  Each obligation goes to
   `synth.lean_backend.verify.verify_class_via_lean`, which
   translates to a Lean theorem and tries to prove with mathlib
   tactics (`omega`, `nlinarith`, `aesop`, `subst_eqs`, ...).  A
   successful Lean proof promotes the class to VALID.
5. **Sound rejection.**  Any class remaining `unknown` after
   steps 1–4 stays in `unknown_deferred` — it is REJECTED for
   purposes of the global SAT search.  If no other valid
   attribute class survives, the constraint as a whole has no
   valid class and synthesis returns `NoSolution`.

## Routing: which kinds go to Lean dispatch

`_AXIOM_HEAVY_DISPATCH_KINDS` in `synth/solver.py` controls which
constraint kinds route through the Lean dispatch pipeline (helper
citation → cache → generic chain).  Currently:

| Kind                   | Path                       |
| ---                    | ---                        |
| `safety`               | Lean dispatch              |
| `safety-bundle-entry`  | Lean dispatch              |
| `safety-bundle-post`   | Lean dispatch              |
| `coverage`             | Lean dispatch (NEW, Phase H.2.CODEGEN — `theorem_for_coverage` via omega/decide) |
| `cost-lb`              | Lean fallthrough on UNKNOWN (Phase COST_INVS §2) |
| `cost-decrement`       | Lean fallthrough on UNKNOWN (Phase COST_INVS §2; chain variant for non-SB bodies) |
| `cost-budget`          | Z3 only (linear in typical encodings) |
| `ranking-lb`           | Z3 only                    |
| `ranking-decrease`     | Z3 only                    |
| `ranking-proc-*`       | Z3 only                    |

**Cost obligations are soundness-critical.**  All three
`cost-*` kinds are members of `_REJECT_UNKNOWN_KINDS`:
synthesis under sound default rejects any class whose cost
constraint remains UNKNOWN after Z3 + Lean dispatch.  This
matches the policy for `safety` / `ranking-*` — proof
obligations don't get a free pass just because they're new.

`ranking-*` stays on Z3 because (a) the obligations are linear
arithmetic Z3 handles in milliseconds, and (b) Lean dispatch's
`lake env lean` per-call overhead (~3-5s minimum) multiplies
fatally over the per-class enumeration count.  See CLAUDE.md
Lesson #46 for the kadane / modexp regression that exposed this.

`coverage` was added to Lean dispatch in Phase H.2.CODEGEN
because Z3 returns spurious UNKNOWN on SB(n>1) coverage
constraints with quantified UF axioms (e.g., kadane's case-split
recurrences).  Lean's omega/decide on the explicit discharge
closes them.

## Translator-vs-Z3 obligation parity (lesson #66)

The chain-aware Lean translator
(`synth/lean_backend/translate.py:_emit_chain_item_hyps`) must
emit a hypothesis set that is **semantically equivalent** to
the Z3-side antecedents emitted by `synth/constraints.py` for
the corresponding obligation.  If Lean emits a STRONGER
hypothesis set than Z3 has, Lean can validate classes whose
Z3-side obligation cannot prove — the verify oracle treats
Lean VALID as a class-valid signal, and the synthesizer
emits cubes whose underlying Z3 obligation is not actually
valid.  This is a SOUNDNESS bug.

The mechanical requirement: every change to which hypotheses
the Z3 constraint includes (or excludes) for an IR construct
must be mirrored on the Lean side.

**Phase K.D, 2026-05-25**: break-capable Loops are now
treated symmetrically on both sides.  The Z3 abstract
transition drops `¬g_inner` for break-capable Loops (early
exit via break may leave `g_inner` true); the Lean
chain-aware translator's `_emit_chain_item_hyps` mirrors
this and no longer emits `¬g_inner` for those Loops.  Before
the parallel fix, Lean had a STRONGER `¬g_inner` premise
that Z3 didn't supply.  See CLAUDE.md "Phase K.D" for the
full story and debug.skill Signal 10 for the diagnostic
recipe.

**Future construct changes**: if a new IR construct adds
similar "exit may have guard still true" semantics (e.g.,
`continue`, exceptions), the Lean-side parity must be
re-checked at the same time as the Z3-side change.  The
parity check is the first thing CI should exercise for any
such change.

## Helper short-circuit semantics

When a Tier-3 helper validates the FULL-τ subset of a
constraint, the solver short-circuits the per-subset
enumeration and emits a SINGLE cube pinning every relevant
indicator True.  Soundness justification:

- The helper has been hand-proven against the full-τ
  hypotheses in `Helpers.lean` (committed, CI-checked).
- The emitted cube reflects exactly the chosen-atom subset the
  helper covers.  No generalization (no "any superset works"
  shortcut in the SAT layer; subset semantics are enforced at
  the cite-matching level instead).
- The cube is added to the constraint's set of valid classes;
  the global SAT search composes it with other constraints'
  cubes as usual.

The trade-off is score-minimization: the synthesized solution
carries the FULL τ atom set rather than a minimal subset that
would also satisfy the constraint.  Per-atom helpers (deferred,
RESEARCH.md task #170) would recover the minimization.

**Full-subset gating (lesson #78).**  When a HelperEntry sets
`required_atoms = frozenset(full subset)`, the helper short-
circuit fires ONLY on the full-subset cube; partial subsets
fall through to the generic Lean tactic chain — which typically
times out into UNKNOWN → sound-mode rejection → ABANDON.  This
is BY DESIGN for benchmarks whose helper proof legitimately
requires every τ atom (e.g., Gale-Shapley's τ@L0 with 8 atoms,
each load-bearing for the multi-case store-update proof).  The
synth produces a solution carrying the full τ subset rather
than a minimized one, trading off score-minimization for
guaranteed soundness via the full-subset helper.  General rule:
declare `required_atoms` as the minimum atom set the proof
actually needs — minimal when the proof factors per-atom (lesson
#71), full when it doesn't.

## Cardinality-ordered enumeration with monotone pruning (ranking-*)

For **ranking obligations** (`ranking-lb`, `ranking-decrease`,
`ranking-proc-lb`, `ranking-proc-decrease`) whose τ has many
atoms (≥10) and all-same-position classification, the solver
uses a cardinality-ordered fallback enumeration after the
Phase 3.L hardest case fails:

- **ANT-only** τ (atoms appear only in antecedents): validity
  is monotone-UPWARD in subset size (a valid subset's
  supersets remain valid).  Enumerate by ASCENDING |S|, stop
  at first valid → that's the minimal valid subset.
- **CONS-only** τ (atoms appear only in consequents): validity
  is monotone-DOWNWARD.  Enumerate by DESCENDING |S|, stop at
  first valid.

The emitted cube pins only the minimal-set atom indicators
(others are left unconstrained); the main SAT layer is free
to combine with any superset without re-verifying.

**Soundness invariant.** The monotone-upward / -downward
property requires:

1. The constraint kind has no τ in the consequent
   (`ranking-lb`/`ranking-decrease` satisfy this by construction:
    the goal is `ϕ ≥ 0` or `ϕ_pre > ϕ_post`, neither references τ).
2. ALL free τ holes share the SAME position (either ALL
   ANT-only OR ALL CONS-only).  Mixed positions across holes
   would break the joint lattice.
3. τ semantics is purely conjunctive (the way our IR encodes τ).

**Mitigation in code.** Before taking the cardinality path,
`solver.py` checks (via `_classify_atoms` + `_free_tau_position`):

```python
_positions = {pos for _, _, pos in free_taus}
_ant_only = (_positions == {False})
_cons_only = (_positions == {True})
_cardinality_path = (
    (_ant_only or _cons_only)
    and sc.kind in ("ranking-lb", "ranking-decrease",
                    "ranking-proc-lb", "ranking-proc-decrease")
    and _flat_count >= 10
)
```

If ANY τ atom is BOTH-position (positions == {True, False})
OR positions are mixed across holes (positions has both),
fall back to the original 2^N enumeration.  The kind
allow-list also keeps this purely structural — the
optimization never fires for `safety` or `safety-bundle-*`
where τ may appear in CONS.

The size threshold (10) is a perf cutoff, not a soundness
gate: small τ holes finish 2^N enumeration faster than the
cardinality overhead.

## `_on_z3_sat` cross-check

After the global SAT layer picks an assignment, the solver
cross-checks each constraint's validity against Z3.  This catches
two failure modes: (a) Lean dispatch verdict drift between
enumeration time and final SAT time, (b) global-SAT-picked
assignments that don't survive a direct Z3 check.

The cross-check is **selective**: it skips kinds in
`_AXIOM_HEAVY_DISPATCH_KINDS` (and additionally skips
`ranking-*`).  Reasons (CLAUDE.md Lesson #49):

- For axiom-heavy safety / coverage, Z3 returns spurious
  UNKNOWN — running it as a cross-check just produces noise.
- For empty-τ ranking constraints, Z3 returns spurious errors
  on under-constrained formulas.  Trust the original Z3
  enumeration verdict.

## The `Problem.potentially_unsound` field

The field is preserved as a **developer escape hatch** for the
benchmark-authoring workflow:

1. Write a new `Problem` with template + atoms + spec.
2. Run synthesis under sound mode.  Likely returns `NoSolution`
   with dumps in `lean/SynthLean/Y2Corpus/<bench>/`.
3. Inspect dumps to confirm the benchmark is structurally
   reasonable (the right obligations are being checked).
4. Curate `.solved.lean` / `.invalid.lean` companions.
5. Re-run sound mode → SolveResult.

If at step (3) you want to confirm the benchmark synthesizes at
all (independent of proof curation), you might be tempted to flip
`potentially_unsound = True`.  Today that flag is a NO-OP — the
lenient fallback was excised — but the field is reserved for
future development affordances we may want to add (e.g.,
auto-curating proofs via a driver-LLM).

**No production benchmark should set `potentially_unsound = True`.**
A CI grep enforces this.

## Compensating safety nets

In addition to the soundness-by-construction guarantee, three
guard rails catch regressions:

1. **Runtime check emitter** (`synth.emit_py` `runtime_check=True`).
   The Python emitter can lower every proof obligation into an
   `assert` call against `synth.proof_runtime`.  If a proof
   contains a subtle bug (e.g., the synthesizer accepted an
   incorrect class via cache drift), the runtime check fires.
   CLAUDE.md Lesson #32.
2. **Solution-count regression** (`Problem.expected_solutions`).
   Every benchmark pins its expected solution count.  A refactor
   that widens the solution set (typically by accidentally
   dropping a constraint) fails CI.  CLAUDE.md Lessons #31, #38.
3. **Subprocess isolation** (`tests/regression.py`).  Each
   benchmark runs in a fresh Python interpreter so Z3 state can't
   leak between benchmarks.  CLAUDE.md Lesson #40.
4. **Y2 corpus mechanical check** (`tests/test_y2corpus.py`).
   Every committed `.solved.lean` / `.invalid.lean` type-checks
   under `lake env lean`.  Drift between an obligation's
   signature and its curated companion is caught.

## API surface

```python
from synth import Problem, solve

PROBLEM = Problem(
    template = ...,
    ...
    # Default: sound.  Synthesizer fails if any obligation can't
    # be verified by Z3 or Lean.  Don't override.
)

result = solve(PROBLEM)
```

## History

- **Lessons #10 + #33** describe the original conservative-
  ACCEPT-on-UNKNOWN policy and its two-pass refinement.  Both
  pre-date the Lean backend.
- **Lesson #32** introduced the runtime-check emitter as the
  safety net for that policy.
- **Ring 2** added the Lean fallthrough verifier — making most
  UNKNOWN classes genuinely verifiable.  The lenient policy
  became the default-OFF opt-in.
- **Chain-bundle Lean translator + curated `.solved.lean` cache**
  (task #134, #135, #136) closed the remaining axiom-heavy gaps
  on factorial / fib / sum_array / array_product / count_zeros.
  All five now sound by default.
- **Lenient fallback excised** — the field stays as a dev
  escape hatch; the production code path is now dead.
- **Phase H.2.CODEGEN** (2026-05-19, Lessons #45-#50) added
  helper-citation as the first stage of the Lean dispatch
  pipeline.  Three previously-intractable benchmarks
  (kadane, majority_element, modular_exponentiation)
  synthesize sound by default.  Routing allowlist banked;
  `theorem_for_coverage` lands; `_on_z3_sat` cross-check
  becomes selective.
- **Phase COST_INVS** (2026-05-22, Lesson #56) extends the
  verifier pipeline to cost-bound obligations.  Three new
  soundness-critical kinds (`cost-lb`, `cost-decrement`,
  `cost-budget`) join `_REJECT_UNKNOWN_KINDS`; `cost-lb` and
  `cost-decrement` route through Lean fallthrough with access
  to `SynthLean.CostLemmas`.  First end-to-end cost-bound
  graph-flavored benchmark
  (`l16_bipartite_matching/bench_glover_verify.py`)
  synthesizes via Tier-3 helper citation.
- **Phase K.D** (2026-05-25, Lessons #66, #67) lands the
  `_break: True` atom for nested-loop early exit.  The Z3
  abstract Loop transition drops `¬g_inner` for break-capable
  Loops; the Lean chain-aware translator's
  `_emit_chain_item_hyps` mirrors this — closing a soundness
  gap where Lean was over-validating relative to Z3's actual
  obligation.  `theorem_for_break_bundle` takes an
  `enclosing_loop_id` parameter; `verify.py` dispatches via
  `_linearize_path` for break bundles.  First L1.6
  augmenting-path search benchmark
  (`bench_aug3_two_loops.py`) synthesizes via 3 Tier-3
  helpers.
- **Phase K.D.W** (2026-05-25, Lessons #68, #69) adds
  per-constraint wedge detection.  `Problem.wedge_threshold`
  (default 30) controls when the solver WARNs (at threshold)
  and ABANDONs (at 2× threshold) enumeration on a
  constraint after that many non-valid Lean dispatches.
  End-of-run returns `NoSolution(reason="needs-helpers")`
  with hints identifying each wedged constraint
  `(kind, loop_id, branch_idx)` + sample failure-dump paths.

  **Soundness**: the wedge detector preserves soundness by
  construction.  An abandoned constraint contributes an
  empty-or-partial valid-cubes list to the main SAT search;
  the main SAT UNSATs the obligation cleanly; synth returns
  `NoSolution` (sound rejection), never an unverified
  solution.  No code path turns an abandoned obligation into
  "presumed valid"; the detector is purely a diagnostic
  short-circuit, not a verdict.  First validated by
  `bench_aug3_three_loops.py` (K.3.2 3-nested) where the
  detector caught a missing sc1 helper on the first run;
  the second run with the added helper synthesized a sound
  solution in 1466s.
- **Slice 2.C** (2026-05-27, Lessons #73, #74, #75) lands
  the first L1.6 max-matching benchmark to ship with REAL
  Lean proofs for all algorithm-step preservation lemmas.
  `bench_max_matching_concrete.py` synthesizes 1 verified
  solution in 131.9s.  **Headline: trust tier reduced from
  Slice 2.B's 5 axioms (matching-machinery + Berge +
  class-restriction) to only 2 axioms (Berge +
  class-restriction); UFs reduced from 4 to 2.**

  **What's no longer trusted** (vs Slice 2.B):
    - `MatchingSize` UF + `mm_size_nonneg` +
      `mm_size_bounded` axioms: replaced by a concrete
      `c : int` counter incremented `c := c + 2` per AP-flip.
      Bounds derive from arithmetic on `c`.
    - `IsMatching` UF: replaced by a 4-atom concrete
      predicate (range / symm / no_self / edge) carried in
      τ at each loop.
    - `mm_flip_preserves_matching` axiom: replaced by a
      **Tier-1 PROVEN Lean theorem** `flip_preserves_im`
      (~120 LOC), case-splitting `kk ∈ {u, v, M v, w}` vs
      otherwise; pointwise store-unfolding + destructuring
      M's 4 IM atoms.
    - `mm_flip_increases` axiom: subsumed by the concrete
      `c := c + 2` increment in the AP-flip branch.

  **What's still trusted** (user-approved):
    - `mm_berge`: Berge's classical theorem.  Multi-day to
      prove in Lean from scratch; out of scope.
    - `mm_termination_implies_no_ap`: class-restriction
      sufficiency claim (the inputs that satisfy our
      precondition admit Berge's hypothesis at termination).

  **Encoding lessons banked**:

  - **Lesson #73 — `no_self` atom is load-bearing for the
    flip-preserves-IM proof.**  When converting an
    `IsMatching` UF to a concrete predicate, the minimum-
    correct atom set is **4** (range / symm / no_self /
    edge), not 3.  Without `no_self` (`M[k] ≠ k` for matched
    k), the predicate admits `M[v] = v`, which breaks AP-
    flip preservation: the case analysis assumes `{u, v, M
    v, w}` are 4 distinct values.  The 3-atom predicate is
    *more permissive* but *unsoundly weak* for the flip
    theorem.  General lesson: when concretizing a UF + axiom
    abstraction, audit which mathematical properties the UF's
    axioms implicitly assumed.

  - **Lesson #74 — FLAT vs chain-aware helper signature
    dispatch (extension of lesson #69).**  Slice 2.C's
    helpers split: sc1/sc6/sc14/sc15 dispatch FLAT (bare
    pre-state names + primed post-state); sc2/sc3/sc9/sc11
    dispatch chain-aware (`<var>_s0`/`<var>_s1` binders).
    The rule: chain prefix to target has only SB items →
    FLAT; otherwise chain-aware.  Mismatches surface as
    Lean's `unknown identifier` errors when the helper
    references binder names not in the translator's output.
    **Smoke-test each helper individually** via
    `verify_class_via_lean` before committing.

  - **Lesson #75 — concrete-predicate τ counts inflate
    enumeration; minimal-required-atoms (lesson #71) is
    essential.**  Slice 2.C's τ@L2 went from 8 atoms (Slice
    2.B's UF) to 12 atoms (4 concrete IM atoms + 8 other),
    so 2^12 = 4096 subsets per safety-check.  Helpers MUST
    declare just the IM atoms they need so per-subset
    enumeration fires them on partial subsets.  Without
    this, sound-mode rejections on partial subsets kill the
    synth on concrete-predicate benchmarks.

  **Soundness rationale**: the Tier-1 promotion of
  `flip_preserves_im` is the load-bearing trust reduction.
  Slice 2.B trusted the user's claim that the 4-store AP-
  flip preserves the matching invariant; Slice 2.C **proves
  it from first principles** under Lean's kernel.  Every
  invocation of the helper at synth time cites the proved
  theorem, not the axiom.  The remaining axioms (Berge +
  class-restriction) are scoped to "classical mathematics
  facts about graph theory", not to specific algorithm steps.

- **Slice 2.B** (2026-05-25, Lessons #70, #71, #72) lands
  three fixes that close the first end-to-end recursive
  maximum-matching benchmark (`bench_max_matching_recur.py`):

  - **Lesson #70 — `chain_paths_local` atom_refs preservation.**
    Soundness-adjacent fix.  The Cartesian-path generator in
    `synth/constraints.py:chain_paths_local` was capturing
    the shared `current_refs` accumulator AND clearing it on
    the first commit, so subsequent yielded paths recorded
    constraints with empty `atom_refs`.  Effect: helper
    short-circuit silently skipped because
    `_extract_loop_id(sc)` fell back to atom_refs and
    returned None.  Cubes for the second Cartesian path were
    therefore emitted WITHOUT a `loop_id` binding — a broken
    invariant (in practice the gating was inferred correctly
    enough that no unsound code shipped on the in-flight
    benchmark, but the invariant violation is fixable by a
    snapshot+restore pattern: snapshot the refs accumulator
    at generator entry, restore per yielded iteration).
    Commit d69ce41.

  - **Lesson #71 — minimal-required-atoms helper pattern.**
    Sound technique for closing partial-subset enumerations.
    A helper that proves a conclusion from a minimal subset
    of τ atoms (e.g., `mm_sc15_coverage` from τ@L0 atom 2
    alone via `exact h_tau_2.symm`) should declare
    `required_atoms` as just that minimal subset.  Per-subset
    enumeration then fires the helper on every τ subset
    that includes the required atoms — eliminating partial-
    subset UNKNOWNs that would otherwise be sound-mode-
    rejected.  Each emitted cube is helper-proved (no
    over-generalization).  This is a strengthening of the
    existing helper short-circuit semantics (see "Helper
    short-circuit semantics" above), not a relaxation.

  - **Lesson #72 — procedure-level coverage routing.**  The
    standard `_extract_loop_id(sc) is not None` filter in
    solver.py's axiom-heavy Lean dispatch gate excluded
    procedure-level multi-branch SB(n>1) coverage
    (`coverage` kind with `loop_id=None`).  Two-line
    carve-out: route these constraints to Lean dispatch when
    the benchmark has axioms.  No soundness implication
    (just routing); without this, axiom-heavy benchmarks
    with procedure-level branching wedge on Z3's quantifier-
    instantiation heuristics.  Commit 01f9cb0.
