# RESEARCH.LEAN.md

Scoping for a Lean 4 proof backend.  Sister document to
`RESEARCH.md` §B (the user's authored vision); this is the
implementer-facing scoping: what's the MVP, what's deferred,
what's the integration shape, what are the open decisions.

`RESEARCH.md` §B already establishes:
- Lean is now the candidate replacement for PINS as the proof
  backend for compressor / encoder benchmarks.
- The full vision is hybrid dispatch (SMT for predicate-
  abstraction shapes, Lean for structural-induction shapes).
- LLM-as-tactic-proposer is the long-term integration model.

This document scopes a tractable first-week-to-first-month
deliverable that gives signal on whether the path is worth
investing in further.

---

## 1. The question we're answering with the MVP

> Can Lean 4 dispatch a class of obligations that our SMT
> backend can't, in a way that integrates cleanly with the
> existing `Problem` API?

Two parts to "gives signal":

- **Capability proof.**  Pick a benchmark SMT *can't do* — LCS,
  grid_paths, or a recursive compressor — and show Lean
  discharges it.  Without this, the "Lean handles things SMT
  can't" claim is vibes-only.

- **Integration shape.**  Show that the Lean path reuses the IR
  (template, predicates, spec) rather than living as a parallel
  universe.  A standalone Lean prover that doesn't share
  infrastructure is research, but not a *backend* for this
  synthesizer.

Either alone is a half-result.  MVP must hit both.

---

## 2. MVP scope — three nested rings

### Ring 1 (must-have): manual-tactic discharge on one obligation

Pick a single safety obligation from a benchmark currently in
the timeout / wedge regime — most natural choice: the
**inductive constraint on grid_paths** (single-equation 2D-DP
recurrence + UF axiom + quantified array invariant).  Write the
Lean proof by hand.  Goal: prove that Lean *can* dispatch this
class of obligation, with no LLM involved.

Deliverable: `synth/lean_backend/`
  - `translate.py` — IR atom strings + chosen Solution → Lean 4
    `theorem ... := by <tactic>` text.  Each chosen τ atom
    becomes a NAMED hypothesis (`h_tau_0`, `h_tau_1`, ...) so
    the emitted theorem reads like a Hoare obligation, not an
    SMT conjunction (see §3.2 below for why).
  - `dispatch.py` — subprocess into `lake build` over the
    `lean/` project, parse success/failure, return
    `Verified | Unverified`.  *Not yet built — Day 6.*
  - The proof tactic chain lives inside the emitted theorem
    (`by <tactic>`).  Simple obligations (ranking-LB) get
    `omega`; harder ones get tactics named in §3.2.
  - Regression test (`tests/test_lean_backend.py`): synthesize
    → translate → `lake build` → assert green.

Outcome: yes/no on "can Lean prove this at all".  ~1 week.

### Ring 2 (should-have): UNKNOWN-fallthrough Lean dispatch + new compressor benchmarks

**Adjusted from the original scoping (2026-05-15).**  The
original Ring 2 was "literal Verifier abstraction with Lean
replacing Z3 per-attribute-class".  After Ring-1 data, that's
architecturally clean but practically marginal — Lean is
~1000× slower than Z3 per check, and a Verifier swap doesn't
expand the benchmark frontier (see north-star "scale" in
memory: handle every HumanEval+/MBPP+ benchmark end-to-end).

**Ring 2's actual deliverable** is *capability expansion*:

1. **UNKNOWN-fallthrough dispatch.**  Z3 runs first (fast); for
   per-class checks Z3 returns `UNKNOWN` on (the axiom-heavy
   slice — fib's recurrence E-matching, grid_paths' inductive),
   the synthesizer falls through to `LeanVerifier`.  Combines
   strengths: Z3 fast for the easy classes, Lean stronger for
   the hard ones.  Replaces the current two-pass UNKNOWN
   fallback (which just accepts all UNKNOWNs at once).

   `Problem.verify_fallback: Literal["accept" | "lean" | "reject"]
   = "accept"`.  Default preserves the current behaviour.

2. **1–2 compressor benchmarks** that exploit Lean's structural-
   induction strength: run-length encode/decode, possibly LZ77-
   shape.  Specs are recursive over the input list; SMT can't
   formulate them cleanly; Lean's tactics (`induction`, `cases`,
   `simp` with custom lemmas) are the natural fit.  These are
   the benchmarks that *demonstrate* the Lean path's
   value-add, not just its compatibility.

**What this gives us.**  After Ring 2:
  - The same benchmark suite (currently 28 quick + 2 slow)
    still works via Z3.
  - Axiom-heavy benchmarks (fib + the previously-wedged
    grid_paths / LCS) become tractable via Lean fallthrough.
  - 1–2 new compressor benchmarks land that ONLY Lean can
    verify.  First time the synthesizer handles a benchmark
    class SMT couldn't.

**Parked (Ring 2.5 / nice-to-have):**

  - **Post-synthesis re-verification** (the "Option B" from the
    Ring-2 scoping discussion).  Lean re-proves the chosen
    Solution end-to-end as a proof artifact.  Useful for
    proof-carrying-code consumers; doesn't expand capability.
    Land if/when a downstream use case asks.

  - ~~**Per-shape tactic templates** to close the last 1/9 of
    grid_paths inner inductive at the translator level.~~
    **Dropped (2026-05-16).** `RESEARCH.md` §D pivots to a
    driver-LLM-in-loop for per-instance proof sketches rather
    than hard-coded per-shape templates.  Same compute budget
    serves both Problem authoring and Lean proof sketching.

Outcome: ~2 more weeks (Ring 1 took ~7 days; Ring 2 has a
similar scope).

### Ring 3 (nice-to-have): LLM-driven tactic proposal

Replace the hand-written `Tactic.lean` with an LLM-driven loop:
- Lean prints the current goal state.
- LLM proposes a tactic.
- Lean checks; if `sorry`-free, done; else, feed the new goal
  state back to the LLM.

This is the actual research thread (LeanDojo / Lean Copilot
shape), and where the bulk of the long-tail work lives.  In
MVP scope only insofar as it shows the system *could* be driven
by an LLM — a single benchmark with LLM-proposed tactics and a
working budget.  Probably needs ~2 more weeks beyond Ring 2,
and most of that is plumbing (Lean state extraction, LLM I/O
protocol, retry logic).

**Recommendation:** Rings 1+2 in the first sprint.  Ring 3 only
after Rings 1+2 give clear positive signal.  If Ring 1 stumbles
(Lean can't actually discharge our benchmarks without massive
effort), drop the whole thread and revisit PINS.

---

## 3. Integration shape

### 3.1 Where does the Lean code live?

Two options:

- **(a) Per-call ephemeral Lean files.**  For each verification
  query, write a fresh `.lean` file with the obligation + tactic
  proof, run `lean` on it, parse stdout.  Stateless, simple.
- **(b) Persistent Lean module with `lake build`.**  Maintain a
  Lean project under `lean/`; each query is a new theorem in
  the project; we extend the project incrementally and `lake
  build` re-checks.

(a) is faster to prototype, slower per-query (lean cold-starts
~1–2s).  (b) is faster per-query once cached but adds project
infrastructure.

**MVP: (a).**  Switch to (b) if per-query cold-start becomes a
bottleneck.

### 3.2 What does the translation look like?

**Decision (Day 2): translate at the IR/atom-string level, NOT
from Z3 expressions.**  Initially the plan was Z3 ExprRef → Lean
— "translate the same expression Z3 sees".  We rejected this
mid-Day-2 because by the time atoms are conjoined into one
`Implies(...)` Z3 expression, the named-hypothesis structure is
gone.  The atom strings the user wrote (`"v == i*i"`,
`"x >= (i-1)*(i-1)"`) are the right granularity: each one
becomes a NAMED hypothesis in the emitted theorem.

Concrete shape for intsqrt's `ranking-LB` obligation:

```lean
set_option linter.unusedVariables false in
theorem L0_phi_lb
    (x i v : Int)                       -- program state binders
    (h_pre  : x ≥ 1)                    -- problem.pre
    (h_tau_0 : v = i * i)               -- chosen tau atoms,
    (h_tau_1 : x ≥ (i - 1) * (i - 1))   --   named individually
    (h_tau_2 : i ≥ 1) :
    x - (i - 1) * (i - 1) ≥ 0 := by     -- chosen phi atom ≥ 0
  omega
```

Sketch for an inductive `safety` constraint (next obligation
kind, Day 3+):

```lean
theorem L0_inductive
    (x i v x' i' v' : Int)              -- pre + post state
    (h_pre   : x ≥ 1)
    (h_tau_0 : v = i * i)               -- pre-state τ
    (h_tau_1 : x ≥ (i - 1) * (i - 1))
    (h_tau_2 : i ≥ 1)
    (h_guard : v ≤ x)                   -- loop guard
    (h_trans_v : v' = v + 2*i + 1)      -- transition
    (h_trans_i : i' = i + 1) :
    -- conclusion: post-state τ atoms.
    v' = i' * i' ∧
    x ≥ (i' - 1) * (i' - 1) ∧
    i' ≥ 1 := by
  <tactic>
```

Post-state variables are emitted as primed names (`x'`, `i'`)
with the transition contributing `h_trans_<var>` hypotheses
relating them to pre-state values.  This makes the symbolic-
execution structure explicit in the theorem text rather than
folding it into one big formula.

Edge cases:

- **`ForAll(lambda k: P)`** in an atom → `∀ k : Nat, P` Lean
  binder inside the corresponding hypothesis.
- **`Update(A, i, v)`** in a transition → `store A i v` (our
  hand-rolled `(Nat → Int) → Nat → Int → Nat → Int` defined in
  `SynthLean/Basic.lean`).  Mathlib's `Function.update` waits
  until we wire mathlib in (Ring 2).
- **Uninterpreted functions** (e.g., `paths(i, j)` in
  grid_paths) declared as Lean `axiom`/`def` blocks emitted
  alongside the theorem.

Most of this is mechanical once the atom-string → Lean
translation table is set; `synth/lean_backend/translate.py:
lean_expr` is the table.

### 3.3 Lean array encoding

Three options:
- (i) `Array Int` (Lean's mutable-style array; uses persistent
  arrays under the hood).
- (ii) `List Int` (pure functional, recursion-friendly,
  natural for structural induction).
- (iii) `Int → Int` (a function — maps cleanest to Z3's
  `Array(Int, Int)` but loses inductive structure).

For grid_paths / LCS (the SMT-wedge benchmarks), the
*recurrence* over `lcs(i, j)` is the load-bearing piece —
the array itself is just a memo.  We can use (iii) for the
array and have `lcs` and `paths` as uninterpreted Lean
functions with axiom-style equations.  This keeps the
translation close to the SMT encoding.

For compressor benchmarks (PINS scope), where the spec is
recursive over the input list, (ii) is the natural fit.

**MVP: (iii) `Int → Int`** — locked in Day 1 (originally as
`Nat → Int`; switched to `Int → Int` Day 3 after array_zero's
ranking-decrease theorem hit a type mismatch).  Program loop
counters are `Int`; using `Nat` for the array index domain would
require `.toNat` coercions at every `store`/`read` call site
that touches a program variable.  `Int → Int` matches the SMT
encoding exactly (Z3's `Array(Int, Int)`) and lets `0 ≤ k`
antecedents in the user's invariants stay meaningful rather than
becoming the trivially-true `0 ≤ k` over Nat.

`store : (Int → Int) → Int → Int → Int → Int` is the array-Store
equivalent, defined in `SynthLean/Basic.lean`.  Mathlib's
`Function.update` (the "real" version with a battery of lemmas)
lands in Ring 2.  Reconsider (ii) when we hit a benchmark that
needs structural induction over the array.

---

## 4. Toolchain

- `lean --version` 4.x (latest stable).
- `lake` for project management (Ring 1 doesn't need this; Ring
  2 might).
- `mathlib` for general arithmetic / array lemmas.  Heavy
  dependency (~1 GB after build); pin a known version.
- Optional: LeanDojo or Lean Copilot for LLM integration (Ring
  3).

Install path on macOS: `elan` (rustup-style installer for Lean
toolchains).  CI: ubuntu-latest has no Lean pre-installed —
need a `setup-lean` step (~30s install).  Adds ~1m to total CI
time, which is fine.

---

## 5. Risks and exit criteria

### Ring 1 risks

- **Lean takes longer than SMT.**  Hand-written tactics for one
  obligation might take 30s of Lean compile time.  Compared to
  the SMT wall (timeout at 10–20 min on this class), still a
  huge win — but worth noting.
- **The grid_paths obligation might just be easier in Lean
  because UF axioms become definitions.**  This is the *point*
  — but it does mean we can't directly compare "Lean vs SMT on
  the same query"; we have to compare "Lean discharges what
  SMT can't".

### Ring 2 risks

- **Translation surface keeps growing.**  Each benchmark might
  surface a new atom shape that needs a Lean equivalent
  (`ForAll` with arrays, `Update`, recursive UF apps,
  uninterpreted-function axioms attached as Lean `axiom`
  declarations).  The translation table lives in
  `synth/lean_backend/translate.py:lean_expr`.  If growth is
  superlinear or a benchmark needs a structurally-different
  shape (e.g., `Update` in a `ForAll` body for a quantified
  array invariant), that's a signal the abstraction isn't
  paying off and we may need a more principled Hoare-style
  embedding instead.
- **The Verifier abstraction leaks.**  E.g., Lean returns a
  proof object; Z3 returns sat/unsat.  Making the interface
  uniform might compromise either.  Acceptable for MVP if the
  abstraction is "verifier returns Valid/Invalid/Unknown"; if
  we need richer info (counter-example models from Z3, proof
  terms from Lean), the abstraction needs refinement.

### Ring 3 risks

- **LLM tactic proposal is its own research project.**  This is
  why it's Ring 3, not Ring 1.

### Exit criteria

- **Ring 1 passes ⇒ keep going.**  If Lean discharges
  grid_paths's inductive constraint with hand-written tactics
  in under a minute of total work, the path is viable.
- **Ring 1 fails ⇒ revisit PINS.**  If Lean can't discharge
  the obligation in any reasonable amount of manual effort,
  the SMT path is what we have and PINS comes back to the
  table.
- **Ring 2 passes ⇒ ship as a flag.**  `Problem.verifier="lean"`
  becomes an option for users who hit the SMT wall.
- **Ring 2 fails ⇒ document the integration gap, downgrade to
  "Lean as an external tool".**  Still useful; not a backend.

---

## 6. Open decisions (need user input)

1. **MVP target benchmark.**  Recommendation: grid_paths
   inductive constraint (cleanest SMT-failure data point).
   Alternative: a run-length-style recursive compressor (closer
   to the PINS-replacement vision, but means writing a new
   benchmark + new Lean idioms in parallel).

2. **Array encoding for MVP.**  Recommendation: (iii) `Nat →
   Int`.  Alternative: (i) `Array Int` if we want to flex the
   Lean array library from the start.

3. **Toolchain in CI from day 1?**  Recommendation: yes — every
   commit that touches `synth/lean_backend/` should be CI-
   checked.  Otherwise bit-rot is inevitable.

4. **LLM-in-loop in MVP?**  Recommendation: no — hand-written
   tactics in Ring 1, defer LLM to Ring 3.  Faster signal;
   smaller surface to debug.

5. **Time box.**  Recommendation: 1 week for Ring 1, 1 more
   week for Ring 2, pause and review before Ring 3.  Total 2
   weeks to make-or-break decision.

---

## 7. Week-1 plan (Ring 1)

| Day | Deliverable                                              | Status |
| --- | ---                                                      | ---    |
| 1   | Install elan + Lean 4 toolchain; Lake project scaffold under `lean/`; smoke test in `SynthLean/Basic.lean` covering literal/tactic/quantified/conditional/array-store shapes; CI integration. | **DONE** (2026-05-15) |
| 2   | `synth/lean_backend/translate.py`: `lean_expr(py_str)` and `theorem_for_ranking_lb`.  End-to-end pipeline (synthesize → translate → `lake build`) green on intsqrt and sumi via `tests/test_lean_backend.py`. | **DONE** (2026-05-15) |
| 3   | `theorem_for_ranking_decrease` (`pre-state τ ∧ guard ∧ trans ⇒ phi(pre) > phi(post)`).  Loop body = SB(n=1), parallel-dict transitions.  Tested on sumi / mul / array_zero via `omega`.  Array encoding switched from `Nat → Int` to `Int → Int` (no coercions at the program-variable / array-index interface). | **DONE** (2026-05-15) |
| 4   | mathlib wired in (`require mathlib from git ... @ "master"` in lakefile; `import Mathlib.Tactic` in Basic.lean).  `theorem_for_safety_inductive` lands.  Tactic chain `subst_eqs; refine ⟨..⟩; all_goals first \| omega \| nlinarith` discharges sumi (nonlinear `2*s' = i'*(i'+1)`) and mul (nonlinear `p' = a*i'`) — exactly the polynomial-expansion class core omega couldn't crack. | **DONE** (2026-05-15) |
| 5   | grid_paths INNER inductive — hand-written.  Foundation: `store2d` in Basic.lean for 2D arrays, `paths` and recurrence/base axioms in a new `SynthLean/GridPaths.lean`.  Tactic chain: `subst h_trans_*`; `refine ⟨…⟩`; per-conjunct dispatch via `omega` / direct hypothesis / case-on-`q = j` with `if_pos`/`if_neg` over `store2d`.  Compiles in 3.2s.  **Ring 1 capability claim validated** — Lean dispatches what SMT couldn't.  Translator emission deferred to Day 6; outer inductive (Seq body) also Day 6. | **DONE** (2026-05-15) |
| 6   | Translator automation foundation: `int[][]` in `_state_binders`, 4-arg `Update` in `lean_expr` (→ `store2d`), `emit_axiom_declarations(problem)`.  Generic tactic chain extended to `first | assumption | omega | nlinarith | aesop | (intros; simp_all [store, store2d]; …)`.  Translator emits the right SHAPE for grid_paths inner inductive; aesop dispatches 8/9 conjuncts but stalls on the column-0-preservation conjunct (needs explicit `by_cases q = j` + `if_neg`).  Test verifies emission correctness; proof-of-concept still lives in hand-written `GridPaths.lean`. | **DONE** (2026-05-15) |
| 7   | Tactic-chain improvements: `(aesop; done)` gating (fixes partial-progress shadowing), `split_ifs` fallback, `solve_by_elim` fallback.  Closes 8/9 conjuncts of grid_paths inner inductive through the translator.  The 9th needs `apply h_tau_X; omega` — generic per-shape templates are Ring-2 work.  End-of-Ring-1 review in `RESEARCH.LEAN.md` §Ring 1.  Recommendation: **go on Ring 2**. | **DONE** (2026-05-15) |
| 6   | `dispatch.py` subprocess wrapper — returns `Verified | Unverified` for a single obligation.  Replaces the test's inline `subprocess.run([lake, "build"])` call. | pending |
| 7   | Document, commit, present at end-of-Ring-1 review.       | pending |

Ring 2's week-2 plan kicks in only after Ring 1 lands.

---

## Status

**Ring 1 COMPLETE (2026-05-15).**  Days 1–7 landed.
Capability claim **validated**; translator dispatches 8/9 of
grid_paths inner inductive (the remaining 1/9 is a tactic-
engineering gap, not a Lean capability gap — the hand-written
`SynthLean.GridPaths` proves it in 3.2s).  Full review:
`RESEARCH.LEAN.md` §Ring 1.  Recommendation: **go on Ring 2**.  Locked-in §6 decisions:

  1. MVP target: **grid_paths inductive constraint.**
  2. Array encoding: **`Int → Int`** with hand-rolled `store`.
     (Originally `Nat → Int` per Day 1; switched Day 3 — see
     §3.3.)  Mathlib's `Function.update` waits until Ring 2.
  3. Toolchain in CI from day 1: **yes.**  Two CI steps live:
     `Lean backend build` (smoke test compiles) and `Lean
     backend tests` (synthesize → translate → `lake build`).
  4. LLM-in-loop: **deferred to Ring 3.**  Ring 1+2 use hand-
     written tactics; emitted theorems use `omega` for the
     ranking-LB obligations covered so far.
  5. Time box: **1 week Ring 1, 1 more week Ring 2, then
     pause-and-review.**

**Mid-course design change (Day 2): translate at the
IR/atom-string level, not from Z3.**  §3.2 updated to reflect.
CLAUDE.md Lesson #39 records the rationale: Z3 is too low; by
the time atoms are conjoined the named-hypothesis structure is
gone.  Atom-strings give Hoare-shaped theorems readable by
humans and proof-tooling alike.

**Ring 2 + Phase Y.1.5 (DONE, 2026-05-17):** Lean integrated as
the verifier for axiom-heavy soundness-critical obligations
(`synth/lean_backend/verify.py`), sound-by-default by every
committed benchmark including the five axiom-heavy ones (`fib`,
`factorial`, `sum_array`, `array_product`, `count_zeros`).

The full translator set:

| Translator                       | Constraint kind            |
| ---                              | ---                        |
| `theorem_for_safety_inductive`   | `safety` (loop inductive)  |
| `theorem_for_ranking_lb`         | `ranking-lb`               |
| `theorem_for_ranking_decrease`   | `ranking-decrease`         |
| `theorem_for_entry_bundle`       | `safety-bundle-entry` (flat)         |
| `theorem_for_chain_bundle`       | `safety-bundle-post` (flat)          |
| `theorem_for_entry_bundle_chain` | `safety-bundle-entry` (chain-aware, #167) |
| `theorem_for_chain_bundle_chain` | `safety-bundle-post` (chain-aware, #167) |
| `theorem_for_coverage`           | `coverage` (Phase H.2.CODEGEN)       |

For SB(n>1) loop bodies, `theorem_for_safety_inductive` and
`theorem_for_ranking_decrease` take `branch_idx` and emit
per-branch theorems (conjoining the loop's guard with the
branch's guard).  `theorem_for_chain_bundle` unions modified-var
sets across all branches for SB(n>1) bodies.

`.solved.lean` / `.invalid.lean` companions in
`lean/SynthLean/Y2Corpus/<bench>/` are consulted as a content-
addressable cache (signature-hash filenames) BEFORE Lean's
generic tactic chain.  Curated proofs become a runtime
verification path, not just training data.

The previously-required `potentially_unsound = True` lenient
fallback has been excised; the field remains as a dev escape
hatch for new-benchmark authoring (no production benchmark
sets it; CI grep enforces).  See `SOUNDNESS.md`.

**Next direction (`RESEARCH.md` §D Phase Y.2, 2026-05-16):**
we explicitly DO NOT invest in per-shape auto-tactic templates.
Instead, the driver-LLM constructs per-instance proof sketches
for obligations Lean's auto-discharge fails on:

  (a) Z3 + Lean generic chain dispatch the easy obligations
      (current path).
  (b) Remaining UNKNOWNs are compiled into Lean files with
      "fill in the proof" scaffolds.  The driver-LLM proposes
      a proof sketch (intermediate `have` lemmas, `by_cases`
      choices, mathlib lemma references).  Sketch → `lean`
      check → iterate on failure.

This subsumes "per-shape templates" as a strategy: instead of
hard-coding tactics per obligation shape (which doesn't scale
to the long tail of benchmark variety), the LLM handles each
instance using the corpus of (English, Problem, proof sketch)
triples built in `RESEARCH.md` Phase X.

**Corpus protocol (2026-05-17).**  `lean/SynthLean/Y2Corpus/`
is the explicit training corpus.  Per-benchmark subdirectories
hold `(failed.lean, solved.lean | invalid.lean)` triples:

  - `.failed.lean` is auto-dumped by
    `synth.lean_backend.verify._dump_failed_obligation` when
    the generic tactic chain fails on a per-class obligation.
    Benchmarks opt in via
    `Problem.dump_lean_failures_dir = "lean/SynthLean/Y2Corpus/<bench>"`.
  - `.solved.lean` is a hand-written proof of the same
    obligation, when the τ subset is actually valid but
    generic auto-tactics aren't enough.
  - `.invalid.lean` is a Lean theorem of the form
    `∃ <vars>, <hyps> ∧ ¬ <goal>` — a mechanically-verified
    existential counterexample showing the τ subset is
    genuinely insufficient and the synthesizer correctly
    rejects it.

CI gate: `tests/test_y2corpus.py` runs `lake env lean` on every
committed companion, so the corpus cannot drift silently when
the translator's encoding changes.  See
`lean/SynthLean/Y2Corpus/README.md` for the full protocol and
current entries.

The mechanical-check insight: prose comments claiming
invalidity are unfalsifiable; an existential counterexample
checked by Lean's kernel is binding.  The driver-LLM trained
on this corpus learns to *construct* counterexamples and
proofs, not just recognize them.

Ring-1 leftovers worth landing alongside the broader plan:
  - **Outer-loop body support** (`Seq` containing a `Loop`)
    via abstract-transition + frame-eqs pattern.  **DONE**
    (#167 chain-aware translators).
  - **End-to-end test** synthesize-via-SMT-verify-via-Lean.

**Stretch corpus Tier-1 push (2026-05-19, 23/28 helpers).**
Yesterday + today landed 23 of 28 post-H.2.CODEGEN Tier-3
helpers as Tier-1 theorems (proved from user axioms +
auxiliary lemmas).  Summary:

| Benchmark              | Tier-1 helpers | Remaining Tier-2 |
| ---                    | :-:            | --- |
| `kadane_max_subarray`  | 2/2  | — |
| `modular_exponentiation` | 2/2 + `pow_mod_base` lemma | — |
| `floyd_warshall`       | 6/6  | `sp_self_nonneg` (Pre assumption) |
| `edit_distance`        | 6/6  | — |
| `insertion_sort`       | 1/1  | — |
| `merge_two_sorted`     | 6/7  | `merge_l2_entry_chain` (precision ceiling) |
| `majority_element`     | 0/3  | `boyer_moore_dominance`, branch helpers (algorithm-trace induction needed) |

The 3 remaining algorithmic axioms are genuine ceilings, not
proof-engineering debt:
  - `boyer_moore_dominance` requires algorithm-trace
    structural induction (strengthened invariant beyond what
    the user's τ can express).
  - `merge_l2_entry_chain` requires strengthening the
    chain-aware abstract Loop transition to propagate
    relational info about loop-body-modified variables.
    See `RESEARCH.md §B.3.5`.
  - `sp_self_nonneg` (FW) encodes the user's
    non-negative-cycles Pre assumption — not algorithmic.

**Authoring pattern**.  The Tier-2-first workflow (axiomatize
to validate E2E, then promote to theorem) and the IR-level τ
gating pattern (REC 11.5 in problem.skill) were both
load-bearing for the 23 promotions.

**Axiom-tightening direction (Slice 2.C, 2026-05-27).**  The
Tier-1 promotion pattern extends beyond `.solved.lean`
companions in the stretch corpus to **algorithm-step
preservation lemmas in axiom-heavy benchmarks**.  Slice
2.C's `bench_max_matching_concrete.py` replaces Slice 2.B's
`mm_flip_preserves_matching` AXIOM with a Tier-1 Lean
theorem `flip_preserves_im` (~120 LOC, case-splitting `kk
∈ {u, v, M v, w}` vs otherwise; pointwise store-unfolding
+ destructuring M's 4 concrete IM atoms).  Trust tier
reduced from 5 axioms (Slice 2.B) to 2 (Berge + class-
restriction only).

The pattern: identify the load-bearing axiom in a UF-heavy
benchmark; concretize the abstracted state (UF →
concrete-atomic predicate, with care for implicit
properties — see lesson #73's `no_self` audit); rewrite
the axiom as a Tier-1 theorem about the concrete data;
update the helpers to destructure the concrete predicate.

This generalizes to any "local mutation preserves
structural invariant" lemma — sorting-network swaps,
matching flips, edit-distance backtrack steps, etc.  Each
axiom displaced is a concrete trust-reduction win.  The
residual axioms (Berge etc.) are scoped to "classical
mathematics facts", not algorithm-step preservation.

---

## §8. Design: nested-loop translator extensions (task #167)

Status: **IMPLEMENTED (2026-05-19)** — validated E2E on
merge_two_sorted (chained loops; ~2 min, 1 solution).  FW
(triple-nested) routes correctly via the chain-aware
translator but needs more chain-aware Tier-2 axioms for E2E
synth.  See CLAUDE.md "Current phase" + lessons #46-47.

Implementation in `synth/lean_backend/translate.py`:
  - `_linearize_path(template, target_loop_id)` — returns
    `(chain_items, target_idx, enclosing_loop_id)`.
  - `_chain_state_binders` + `_emit_chain_item_hyps` — per-
    state binder `<var>_s<k>` plus per-item hypotheses (SB:
    trans + frame; Loop: τ_inner + ¬g + frame).
  - `theorem_for_entry_bundle_chain` (#167.2) and
    `theorem_for_chain_bundle_chain` (#167.3) — chain-aware
    bundle-entry / bundle-post translators.
  - `verify.py` dispatch — routes to chain-aware when
    chain[:target_idx] has non-SB items OR target nested.

Original design notes (problem statement, constraint shapes,
implementation plan) preserved below for the historical
record.

### 8.1 Problem

`theorem_for_entry_bundle` and `theorem_for_chain_bundle` assume
the loop they target is at the TEMPLATE'S TOP LEVEL — i.e., the
template is `SB(init)* >> Loop(<loop_id>) >> SB(skip)*`.  For
top-level loops these translators work and have been validated
on kadane / majority / modular_exp / FW's L0.

But FW (and edit_distance, and any future multi-loop algorithm)
has NESTED loops:

  FW: `SB(B0) >> Loop(L0 of: SB(B1) >> Loop(L1 of: SB(B2) >>
       Loop(L2 of: SB(B3, n=2)) >> SB(B4)) >> SB(B5))`.

For L1's `safety-bundle-entry` and `safety-bundle-post` the
synth emits constraints whose body spans the OUTER loop's
context (τ@L0 ∧ g@L0 ∧ ...) — but the current translators
fail with:

  - **`theorem_for_entry_bundle`**: "no SB(init) block found
    before loop" — it looks for an init SB at the top level
    of `_linearize(problem.template)`; for L1, the init is
    SB(B1) WITHIN L0's body, not at top level.
  - **`theorem_for_chain_bundle`**: "loop L1 not in template"
    — same reason; `_linearize` doesn't recurse into Loop
    bodies, so it doesn't see L1.

### 8.2 Constraint shapes (from constraints.py)

`emit_bundle_to` in `constraints.py` emits two shapes:

  1. **safety-bundle-entry(L)**:
       `Fpre ∧ <chain prefix to L's entry state> ⇒ τ_L(entry)`
     For a NESTED loop L inside outer loop O:
       `τ_O ∧ g_O ∧ <chain from O-body-entry to L-entry>
        ⇒ τ_L(at L's entry state)`

  2. **safety-bundle-post(L)**:
       `Fpre ∧ <full chain through L> ⇒ <target>`
     For a NESTED L inside O:
       `τ_O ∧ g_O ∧ <chain from O-body-entry through L's
                    abstract transition and beyond>
        ⇒ τ_O'`  (next iteration of O — the outer τ at the
                  end of O's body chain)

The "chain" includes:
  - SBs (concrete transitions).
  - Nested Loops as abstract transitions:
    `τ_inner(it_out) ∧ ¬g_inner(it_out) ∧ frame_eqs`
    (vars NOT modified by inner loop's body are preserved).

### 8.3 What the translator needs to do

Given a SafetyConstraint for `safety-bundle-{entry,post}` on a
NESTED loop L:

  1. **Locate L's containing context.**  Walk
     `problem.template` to find L; record the enclosing
     `Loop(O)` (if any).  L's chain = the Seq containing L
     (which is O's body, or transitively further out).

  2. **Identify the chain items.**  Within the enclosing
     context, items before L are inits; items after L are
     skips.  Each item is either an SB (concrete transition)
     or a Loop (abstract transition).

  3. **Emit binders.**  Pre-state vars at the start of O's
     iteration are unprimed.  Vars modified along the chain
     get primed AT THE STATE WHERE THEY FIRST GET WRITTEN.
     Concretely:
       - For each chain item, allocate FRESH primed names per
         var the item modifies (or per Loop's modified_vars).
       - String the named state through the chain: state_0 →
         state_1 → ... → state_N where N = number of chain
         items.
       - Final state is what's checked against the target.

  4. **Emit τ_O ∧ g_O hypotheses.**  For nested L, the outer
     loop's invariant τ_O AND guard g_O are part of the
     antecedent (we're inside O's iteration).

  5. **Emit chain transitions.**  Each item:
       - SB(n=1): `h_trans_<var>: <var>' = <rhs over previous state>`.
       - SB(n>1): per-branch enumeration (already handled by
         existing translators via branch_idx).
       - Loop(L_inner): abstract transition
         `h_inner_tau: τ_L_inner(it_out) ∧ h_inner_neg_g: ¬g_L_inner(it_out)
         ∧ h_frame_<var>: <var>_out = <var>_in for var ∉
         modified_vars(L_inner.body)`.

  6. **Emit goal.**  For bundle-entry: `τ_L(at L's entry
     state)`.  For bundle-post: `τ_O(at next iteration)` OR
     `Fpost` for outermost.

  7. **Tactic chain.**  Default generic (omega / nlinarith /
     aesop / simp_all + user_axioms).  Helper short-circuit
     fires if the benchmark's helper_registry matches.

### 8.4 Implementation steps

  1. **Refactor `_linearize` to support nested context.**
     New helper `_linearize_path(template, target_loop_id)`
     returns the chain of items in the ENCLOSING Seq of the
     target loop, plus the enclosing Loop's outer-context
     info (`τ_O ∧ g_O` hypotheses).  Returns:
       ```
       enclosing_loop: Loop | None  -- outer Loop if nested
       chain_items: list[Template]  -- items in target's
                                       containing Seq
       target_index: int            -- where target_loop sits
       ```

  2. **Extend `_state_binders` to thread state through
     chain.**  New function `_chained_state_binders(items,
     up_to_idx)` builds primed-var names per state on the
     chain.  Returns:
       ```
       binders: list[str]            -- (n_0 i_0 ... : Int) for each state
       state_at: dict[int, dict]     -- state_idx -> {var: name}
       ```

  3. **Generalize `theorem_for_entry_bundle`**:
       - Use `_linearize_path` to find target context.
       - If enclosing_loop is not None, emit `h_outer_tau` and
         `h_outer_g` binders for τ_O ∧ g_O.
       - Emit chain transitions up to target_index using
         `_chained_state_binders`.
       - Goal = τ_L_target at the state immediately after the
         last item before L.

  4. **Generalize `theorem_for_chain_bundle`**:
       - Similar, but goal = τ_O at the END of the chain (or
         Fpost for outermost).
       - Includes ALL chain items including target L as an
         abstract transition (τ_L ∧ ¬g_L + frame_eqs).
       - The `safety-bundle-post` constraint for L's bundle is
         what proves L's contribution to O's overall safety.

  5. **Frame eqs for abstract loop transitions**.  Use
     `_modified_vars_of_template(L_inner.body, problem)` (already
     exists in constraints.py:891) to compute which vars are
     preserved.  Emit `h_frame_<var>: <var>_out = <var>_in` for
     each preserved var.

### 8.5 Test surface

Add to `tests/test_lean_backend.py`:

  - `test_fw_l1_bundle_entry_emits`: synthesize FW (or stub it
    out), call `theorem_for_entry_bundle` for L1, assert the
    emitted theorem text contains: τ@L0 hyp, g@L0 hyp, SB(B1)
    trans, and concludes τ@L1 at L1's entry state.

  - `test_fw_l1_bundle_post_emits`: similar; assert chain
    threads through L1's abstract transition.

  - `test_fw_l2_bundle_entry_emits`: doubly-nested case;
    chain has τ@L0 ∧ g@L0 ∧ SB(B1) ∧ <abstract trans of L1>
    ∧ SB(B2) ⇒ τ@L2.

  - `test_fw_l2_bundle_post_emits`: similar.

Then `tests/test_helper_codegen.py` extension: register a stub
helper for one of these constraints and assert via_helper=True.

### 8.6 Effort estimate

  - **`_linearize_path`** and **`_chained_state_binders`**:
    ~80 LOC.  Read-only walks.
  - **`theorem_for_entry_bundle` generalization**: ~120 LOC.
    Most logic already exists; need to thread state binders +
    add outer-loop hypothesis emission.
  - **`theorem_for_chain_bundle` generalization**: ~150 LOC.
    Slightly more involved (abstract-transition emission for
    each Loop in chain).
  - **Frame-eqs emission**: ~30 LOC, reuses
    `_modified_vars_of_template`.
  - **Tests**: ~80 LOC.
  - **Iteration on FW E2E**: variable, probably 1-2 days of
    debugging.

**Total**: 2-3 days of focused work.

### 8.7 Risks

  - **Frame-eq correctness**: easy to over-approximate (preserve
    too many vars → constraints too weak) or under-approximate
    (preserve too few → vacuously unsound).  `_modified_vars_of_template`
    is the standard source; verify behavior on FW's nested case
    matches what constraints.py's abstract transition emits.

  - **Goal shape divergence**: the bundle-post goal for a
    nested loop targets the OUTER τ at end-of-chain.  Need to
    ensure the translator's goal MATCHES what the synth's
    SafetyConstraint actually emits.  The synth's `body` field
    is the ground truth — could even pretty-print it for the
    Lean theorem instead of reconstructing from problem.template.
    Worth considering as a fallback strategy.

  - **Helper signatures**: helpers I wrote for FW
    (floyd_warshall_outer_inductive, middle_inductive, etc.)
    were designed against the IDEAL theorem shape.  Once the
    translator emits the ACTUAL shape, the helpers may need
    signature adjustments to match.

### 8.8 Unblocks

  - **floyd_warshall**: all 14 safety constraints currently
    routed to the broken translators.  Once translator works,
    helper short-circuit fires + generic chain handles the
    rest → E2E.
  - **edit_distance**: same shape (nested 2D DP).  Pure win.

### 8.9 Sequencing relative to current state

This is the next major Lean infrastructure item after
H.2.CODEGEN.  Can land independently of the per-atom helpers
work (task #170, DEFERRED).  Recommended ordering:
  - First: this (task #167) — multi-day, unblocks 2 stretch
    benchmarks.
  - Second: per-atom helpers (task #170) — when score-min
    becomes important OR a benchmark's helper doesn't fire
    on its synth's chosen subset.

---

## Ring 1 — end-of-MVP review (merged from lean/RING1_REVIEW.md, 2026-06-07)

**Status (2026-05-15):** Days 1–7 complete.  Capability claim
validated; translator automation 85% of the way to full
auto-emission.

## What we set out to answer

From `RESEARCH.LEAN.md` §1:

> Can Lean 4 dispatch a class of obligations that our SMT
> backend can't, in a way that integrates cleanly with the
> existing `Problem` API?

Two parts:

1. **Capability proof** — pick an SMT-failure benchmark, show
   Lean discharges it.
2. **Integration shape** — show the Lean path reuses the IR.

## Capability proof: ✓

`benchmarks/grid_paths.py` wedges the SMT path past 10 minutes
(documented in `RESEARCH.md` §O as an edge-of-feasibility
research data point).  Its inner-loop inductive obligation —
quantified invariants over a 2D array composed with a UF
recurrence axiom — compiles in **Lean in 3.2s** with a
30-line hand-written proof (`lean/SynthLean/GridPaths.lean`).
The structural moves: `subst h_trans_*`; `refine ⟨…⟩`; `by_cases
q = j` for the just-updated cell; `if_pos`/`if_neg` for
`store2d` reduction; `paths_rec` axiom application; direct
hypothesis dispatch for the rest.

Validates the Ring 1 bet: when SMT hits its quantifier-
instantiation ceiling on 2D + UF + axioms, Lean's tactic engine
— with mathlib's `paths_rec`-style axioms directly usable as
rewrites — dispatches the obligation cleanly.

## Integration shape: ✓ (mostly)

The translation pipeline reuses the synthesizer's IR end-to-end:

```
Problem (atoms + template)
    │
    ├─→ expand()                    (existing)
    │       sets block_id / loop_id
    │
    └─→ synth.lean_backend.translate:
            theorem_for_ranking_lb       — Day 2
            theorem_for_ranking_decrease — Day 3
            theorem_for_safety_inductive — Day 4
            emit_axiom_declarations       — Day 6
```

The user's atom strings become NAMED Lean hypotheses
(`h_tau_0`, …, `h_tau_8`).  The translator handles:

- Scalar program state (`Int` binders).
- 1D arrays (`Int → Int`).
- 2D arrays (`Int → Int → Int` via `store2d`).
- Parallel-dict transitions with primed-var binders.
- ForAll / Exists quantifiers (Int-bound).
- Update / Update2D as `store` / `store2d`.
- UF declarations and axioms.

**Restriction:** loop body must be `SB(n=1)` with a parallel-
dict transition.  Outer loops with `Seq` bodies (e.g.,
grid_paths's outer loop = `SB >> Loop >> SB`) are NOT yet
supported — the abstract-inner-Loop frame-equation pattern
from `synth/constraints.py` hasn't been ported.  Ring 2 work.

## Tactic-chain coverage

| Obligation kind | Linear cases | Nonlinear cases | 2D + UF + ForAll |
| --- | :-: | :-: | :-: |
| ranking-LB        | ✓ omega    | ✓ omega-opaque  | n/a            |
| ranking-decrease  | ✓ omega    | (deferred — Day 4+ scope; needs nlinarith hint) | n/a |
| safety-inductive  | ✓ omega    | ✓ subst_eqs; nlinarith | **8/9 of grid_paths inner conjuncts** |

The remaining 1/9 needs `apply h_tau_X; omega` — pick the
matching pre-state hypothesis and discharge its side condition
via omega.  Generic automation candidates tried:

- `aesop` — partial progress; doesn't try omega-side-conditions
  on hypothesis applications by default.
- `solve_by_elim` — applies hypotheses but doesn't bridge the
  arithmetic side-condition gap.
- `simp_all [store2d]` + `split_ifs` — unfolds correctly but
  leaves the apply-with-omega goal.

What WOULD close it: per-obligation tactic templates that the
translator emits based on the conclusion's structure
(quantified ForAll over array indices touched by Update →
intro + by_cases + apply matching h_tau + omega).  That's a
larger surface than Day 7's time-box.

## What's banked

- **`lean/` Lake project** with pinned `leanprover/lean4:
  v4.30.0-rc2` toolchain.
- **mathlib** pinned via lake-manifest; CI auto-installs the
  pre-built olean cache.
- **`SynthLean/Basic.lean`** with `store` (1D) and `store2d`
  (2D) helpers.
- **`SynthLean/GridPaths.lean`** as the hand-written
  capability-claim reference.
- **`synth/lean_backend/`** translator: three obligation kinds,
  axiom emission, 2D / quantifier / Update support.
- **`tests/test_lean_backend.py`** — 10 tests, all green.
- **CI integration** via `leanprover/lean-action@v1`.

## Encoding lessons banked

- **#39**: For backend ports, stay at the level of user-
  authored abstractions (IR atom strings), not the SMT
  compilation thereof.  Named hypotheses make theorems
  readable; flat conjunctions don't.
- **#40**: Z3 state leaks across in-process synthesis runs.
  Subprocess isolation is the only sound regression strategy.
  (Banked during the Day 4 → Day 5 transition; not strictly a
  Ring 1 lesson but came up alongside.)
- **#41**: Hand-writing the target proof first is the right
  Day-5 move.  Iterating tactics in a hand-written setting
  surfaces the right structural moves that the translator
  should auto-emit.
- **#42**: Generic tactic search has a ceiling.  aesop gets ~80%
  on array-Store inductives; the case-on-the-updated-cell
  pattern needs per-shape templates.

## Go / no-go on Ring 2

**Go.**  Ring 1 validates that Lean can dispatch SMT-failure
obligations and the translation infrastructure can be built
on top of the existing IR.  The remaining gap (closing the
last 10% of obligations) is a tactic-engineering problem, not
a capability problem.

Ring 2 scope (per `RESEARCH.LEAN.md` §2):

1. `Verifier` abstract base; `Problem.verifier` selects.
2. `Z3Verifier` (existing) + `LeanVerifier` (new).
3. End-to-end synthesis using Lean as the verifier for at
   least one benchmark.

Plus the Ring-1 leftovers worth landing during Ring 2:

- **Per-shape tactic templates** for the array-Store-update
  pattern.  Likely close the grid_paths inner inductive fully
  through the translator.
- **Outer-loop body support** (`Seq` containing a `Loop`) —
  the abstract-transition + frame-eqs pattern from
  `constraints.py`.
- **End-to-end test** that synthesizes via the SMT path on a
  simple benchmark and verifies via the Lean path.

## What's out of scope for Ring 2

- LLM-in-loop tactic proposal (Ring 3 per scoping doc).
- Mathlib version-bumping policy.  Currently pinned to master;
  Ring 2 should pin to a stable tag.
- Performance optimization of the Lean build on CI (currently
  ~3 min cold, ~30s warm — acceptable for now).
