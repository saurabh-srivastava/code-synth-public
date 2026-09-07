# Is Claude a good research assistant?

An experience report from building a clean-room reimplementation of
the POPL'10 + PLDI'11 proof-theoretic synthesizer ("Pragna") using
Claude Code as the implementation partner.  The goal of this
writeup is to share what worked, what didn't, and what surprised me
about working with a coding agent on real research-engineering.

The project's north stars (full statement in `README.md` / `DESIGN.md
§0`):

1. **From correctness to full resource semantics.**  Today: prove
   correctness + termination from English.  Target: extend to
   worst-case runtime and space-complexity proofs (PLDI'09-style
   resource templates over the same IR).
2. **From single function to full programs.**  Today: one function
   per `Problem`.  Target: multi-function programs with
   synthesized interfaces + assume-guarantee composition.
3. **Discovery of novel programs.**  POPL'10's Strassen template
   already surfaced 7-multiplication 2×2 matrix multiplications
   not in the literature.  Long-horizon: synthesize provably-
   correct + provably-resource-optimal programs from English
   where the realization may be new.

The HumanEval+/MBPP+ scaling work (Phase X) and the Lean backend
(Phase 6+) are the **bridges** toward these north stars, not the
destination.

*Target length: 5–8 pages.  Trim toward the most-interesting bits
for a technical audience as the document grows.*

## Why this report

I am the first author of both papers.  The Pragna codebase is lost.
A clean-room reimplementation gives me a chance to (a) modernize the
abstractions (Python eDSL → Z3 with Lean as a backend, instead of
annotated-C + clang + custom solvers), (b) push toward HumanEval+/
MBPP+-scale benchmarks, and (c) explore an LLM-driven front end
that lifts English specs to `Problem` objects.

Claude does most of the line-by-line coding.  I do the design,
the corrections, the steering.  The interesting research question
isn't "can Claude write code" (it can) but "can Claude carry a
multi-phase research project, where the right design decision
depends on context Claude doesn't have until the previous phase's
results come in?"

## Case studies (work-in-progress)

> Update this section as case studies surface.  Each entry should
> answer: what was the decision point, what evidence surfaced it,
> how was it resolved, and what does it say about the partnership.

### CS-1.  Mechanically-checked corpus over prose

**Context.**  The Phase Y.2 driver-LLM needs training data: pairs of
(failed Lean obligation, hand-written companion).  My first draft of
the corpus used prose `.invalid.lean` comment files explaining why a
given attribute-class subset was unprovable.

**My pushback.**  "Is it not possible to phrase the counterexample
as a lean proof rather than writing it as a comment?  if phrased as
an invalidating proof then lean can check it, otherwise we have to
rely on the driver-llm's capabilities to read the counterexample
comment and infer that the theorem is invalid; instead of *proving*
that it is invalid."

**Resolution.**  We restructured `.invalid.lean` to prove
`∃ <vars>, <hypotheses> ∧ ¬ <goal>` — a mechanically-checked
existential counterexample.  CI runs `lake env lean` on every
companion, so the corpus cannot drift silently.  This shifts the
driver-LLM training task from "infer invalidity" to "construct
counterexample".

**What Claude did well.**  Accepted the pushback immediately, tested
the pattern on `sc1_fallthrough_class_0`, confirmed it compiles,
proposed the CI gate, then proactively switched all 6 prose
companions to Lean-checked negations.

**What Claude missed first time.**  The original prose pattern
*looked* fine — it had a counterexample described in detail.  The
gap between "described counterexample" and "mechanically-checked
counterexample" is exactly the kind of soundness gradient that
needs human flagging.  A pure-LLM workflow would have shipped the
prose version and only caught the gap later (or never).

### CS-2.  Solution-count drift as a free soundness oracle

**Context.**  Phase 5.B+ centralized SB-constraint emission.  After
the refactor, `rec_zero_array` went from 1 → 3 solutions, including
two with non-decreasing recur args (synthesized C would
stack-overflow).

**Surface.**  The regression suite already printed solution counts
per benchmark — but the check was informational.  Claude noticed
the count drift in the output and traced it to a generator
exhaustion in `emit_recur_decrease` (the inner per-atom loop
iterated a generator that emptied after the first atom).

**Resolution.**  Materialize the generator at function entry
(`paths_list = list(paths_to_in_b)`).  Then promote the
solution-count check from informational to a hard guard:
`Problem.expected_solutions: int | None = None`.  Now any future
refactor that widens the solution set (by dropping a soundness
constraint) fails CI immediately.

**What this case shows.**  Soundness signals are often free if you
make them explicit.  Claude was good at:
- Noticing the drift in regression output.
- Tracing it to a specific bug.
- Proposing the explicit-annotation guard.

Claude wasn't proactive about *promoting* informational checks to
hard guards — that came from explicit prompting ("we should make
this a CI failure, not a note").  This is a recurring pattern:
Claude implements what's asked but doesn't always escalate
opportunistic improvements.

### CS-3.  Z3 unsoundness on axiom-heavy: spiral and resolution

**Context.**  Factorial / array_product / fib have universal axioms
over uninterpreted functions (`fact`, `prod`, recurrences).  The
synthesizer accepted "smaller τ" solutions that omit the recurrence
atom (`result = fact(i-1)`) — the synthesized code is correct, but
the proof is incomplete.  Lenient mode (`potentially_unsound = True`)
masked the issue.

**Spiral.**  We tried multiple architectures:
1. **Sound mode + .invalid.lean cache only** → factorial UNSATs
   (Z3 returns UNKNOWN on valid classes, cache only handles
   invalids).
2. **Add ANT-only enumeration fallback** → factorial synthesizes
   but with an unsound τ (Z3 falsely accepts the post-bundle
   obligation due to axiom misinstantiation).  Reverted.
3. **Skip Z3 entirely for axiom-heavy + soundness-critical** →
   route all to Lean with parallel dispatch.  Works for some
   constraints, but the post-bundle safety constraint has
   `loop_id=None` and falls back to Z3 → same unsoundness.

**Resolution.**  After several false starts, the actual root cause
turned out to be deeper than initial framings:

The Lean translator's `theorem_for_safety_inductive` constructs
a LOOP INDUCTIVE theorem `τ ∧ g ∧ trans ⇒ τ'` from the
SafetyConstraint's metadata.  Chain-bundle safety constraints
(`init + abstract loop transition + skip ⇒ Fpost` — sc#4 in
factorial) ALSO had kind="safety" but encode a different
obligation.  Routing them through the same translator generated
a wrong-theorem Lean call that Lean correctly proved — but the
synthesizer was unsoundly accepting because the proven theorem
wasn't the actual obligation.

The full fix landed in three layers:

1. **Split the kind** (`safety` → `safety` + `safety-bundle-entry`
   + `safety-bundle-post`).  Each sub-kind has a distinct
   theorem shape.
2. **Write two new translators**: `theorem_for_entry_bundle`
   (`Fpre ∧ init ⇒ τ_loop`) and `theorem_for_chain_bundle`
   (`Fpre ∧ τ_exit ∧ ¬g ⇒ Fpost`).
3. **Curate the chain-bundle proof** as a `.solved.lean`
   companion when Lean's generic chain can't close it.

Result: factorial synthesizes under `potentially_unsound = False`
in 8 minutes, picking the SOUND τ
(`result = fact(i-1) ∧ i ≥ 1 ∧ i ≤ n+1`) that the previous
unsound run had been dropping the recurrence atom from.  Code
correct AND proof correct.

**Generalization.**  After validating factorial, the same pattern
extended to **fib (7 min), sum_array (3 min), and array_product
(7 min)** with one hand-written `.solved.lean` per benchmark for
each of sc#1 and sc#4.  Total curation effort: ~30 minutes per
benchmark.

**count_zeros — closing the last gap.**  count_zeros has an
`SB(n=2)` inner body (case-split on `A[k] == 0`), so the
single-branch translator didn't apply.  The extension —
`branch_idx` on `SafetyConstraint`, per-branch
`theorem_for_safety_inductive` (conjoining loop guard with
branch guard), and union-of-modified-vars in
`theorem_for_chain_bundle` for `SB(n>1)` bodies — was a couple
hundred lines but architecturally clean.  count_zeros now
synthesizes sound in 26 minutes; ALL FIVE axiom-heavy
benchmarks (`factorial`, `fib`, `sum_array`, `array_product`,
`count_zeros`) are sound by default.

**Final action: excise the lenient fallback.**  With no
production benchmark needing `potentially_unsound = True`, the
solver's two-pass lenient promotion was now dead code.  We
deleted it and replaced it with a CI grep guard: any commit
that sets `potentially_unsound = True` on a benchmark file
fails CI.  The Problem field remains as a documented dev
escape hatch (no current production usage; reserved for
future dev affordances).

**What this validates about Claude as a research partner.**  The
mechanically-checked corpus + chain-bundle translator + parallel
Lean dispatch is the kind of multi-layer infrastructure that
exists for ONE PURPOSE — to enable sound synthesis of axiom-heavy
programs.  Building it required:
- The user driving the high-level architecture decisions
  (mechanically-checked over prose, route axiom-heavy through
  Lean, split safety-bundle kinds).
- Claude implementing each piece end-to-end (translator,
  cache lookup, signature hashing, dispatch wiring).
- A tight feedback loop where each failed test surfaced the
  next layer of the gap (Z3 unsoundness → translator
  mismatch → chain-bundle obligation → curated proofs).

In one focused session, factorial moved from `NoSolution under
sound mode` to fully sound, then the same pattern scaled to
three more benchmarks in the next push.  That's the leverage
of the partnership: ONE careful implementation sets up a
template that subsequent benchmarks ride on.

**What Claude did well.**  Followed the user's direction
("skip Z3 entirely for axiom-heavy") with a concrete implementation
(parallel ThreadPoolExecutor dispatch, capped at half CPU count).
Self-correctly identified that the ANT-only fallback exposed Z3
unsoundness without fixing the root cause and reverted it.  When
the user asked "we handled the bug right?  we didn't forget about
it", went back, traced the translator gap, and split the
constraint kind to make the limitation honest.

**What Claude got wrong twice (then a third time).**  Initially
declared "factorial under sound mode SYNTHESIZES!" before
checking whether the chosen τ actually proves the post.  The
synthesized code was correct (factorial computes correctly),
but the *proof* (the chosen τ atoms) was insufficient.  Then,
after fixing the obvious loop_id=None bug, ran factorial again,
got the SAME unsound τ, and only after reading the .failed.lean
dump did the deeper translator-mismatch root cause surface.
Third instance: after the safety-bundle split (which correctly
made factorial UNSAT under sound mode), I added four
`.solved.lean` files for sc#1's valid τ subsets thinking that
would unblock synthesis.  It didn't — and only after dumping
per-constraint cubes did the next layer surface: sc#4
(post-bundle, Z3-routed) has 6 valid cubes, all of which have
at least one single-hot indicator set to False (the "vacuous
antecedent" path Z3 spuriously proves UNSAT on).  The all-True
single-hot case — the only one well_form admits — returns Z3
UNKNOWN, which under sound mode rejects.  Net: sc#4 contributes
zero globally-feasible cubes; SAT is unsatisfiable.

Twice declaring success before actually verifying soundness is
exactly the failure mode a proof-theoretic system must avoid.

**Lesson for the partnership.**  In soundness-critical work,
"success" needs to be defined precisely.  "Synthesizer returns
SolveResult" is not the same as "synthesizer produces a sound
proof".  The discipline of stating success conditions explicitly
upfront — before the test runs — would have caught this faster.
Even better: a soundness oracle (e.g., a Lean-verified end-to-end
proof artifact) would catch the unsound-acceptance class
automatically, similar to how the runtime-check emitter caught
the Z3-UNKNOWN-as-valid bug for max_array.

**Lesson for the architecture.**  The translator's contract was
implicit: "construct a Lean theorem from (constraint kind, chosen
atoms)".  But the *theorem shape* depends on the constraint's
ROLE in the synthesis (loop-inductive vs chain-bundle vs
ranking-*), and "kind" alone wasn't a fine-enough discriminator.
Refining the kind taxonomy (`safety` → `safety` + `safety-bundle`)
made the gap explicit and surfaced what the translator owes the
solver.

### CS-4.  The leverage of a settled architecture

**Context.**  After CS-3 closed factorial, fib, sum_array,
array_product, count_zeros, and ALL sound-mode work landed, I
added one more axiom-heavy benchmark — `count_equal` — as part
of a Phase X corpus push.  count_equal is structurally
identical to count_zeros: same case-split UF recurrence (now
parameterized by a target value `t` instead of the constant
`0`), same SB(n=2) branched body, same template shape.

**The contrast.**  count_zeros took most of a session to get
working under sound mode: design the chain-bundle translator,
extend it for SB(n>1) bodies, curate proofs, iterate when
proofs failed, etc.  count_equal took **about 15 minutes**.

The workflow:

1. Write the `Problem` (5 minutes, copy-paste-adapt from
   count_zeros).
2. Compute the three signature hashes (sc#2 branch 0, sc#4
   branch 1, sc#7 chain-bundle post) via a one-line Python
   invocation.
3. Copy count_zeros's three `.solved.lean` files, rename to
   the new hashes, change `count` to `count_eq` and add the
   `t` parameter to the axiom signatures.
4. Type-check via `lake env lean` — all three pass first try.
5. Add to slow regression, commit.

No new translator work.  No new dispatch wiring.  No new
debugging session.  The architecture from CS-3 absorbed the
new benchmark without any code changes.

**The principle.**  Phase Y.1.5 was foundational, not local.
The translator + cache + dispatch machinery was painful to
build but compounds across every subsequent axiom-heavy
benchmark.  The next 10 axiom-heavy benchmarks won't cost 10×
count_zeros — they'll cost 10× count_equal.

**What this validates about the partnership.**  Multi-step
foundational work is exactly where Claude + careful human
review wins.  The foundation took ~5 hours of focused
collaboration with multiple wrong turns surfaced through tight
iteration (see CS-3's "wrong three times" note).  The
follow-on cost — applying the foundation to a structurally
similar problem — is ~15 minutes of mostly-mechanical work
Claude can do solo.  That's the lever: invest in the
foundation, then ride it.

**What Claude could do better.**  The hash-computing
one-liner in step (2) is currently a copy-paste recipe; it
should be a `synth lean-hash <benchmark> <constraint>`
CLI command (or a `python -m synth.lean_backend.translate
--hash benchmarks/count_equal.py`).  Claude could
proactively factor this out — at the point we're computing
hashes the third time for the third axiom-heavy benchmark in
a session, the abstraction is clearly load-bearing.  Instead
Claude (me) hand-rolled the same invocation for fib,
sum_array, array_product, count_zeros, count_equal.  Five
times.  Worth banking as a pattern: *if I find myself
copy-pasting an invocation more than twice, escalate to a CLI
or function*.

### CS-5.  Binary search: a capability gap, three rewrites, one workaround

Phase X.S includes `binary_search` as one of the five "hardest
HumanEval+/MBPP+ representatives".  Claude wrote the obvious
classical implementation: a single loop, three guarded branches
(`A[mid] == x`, `<`, `>`), and a `found` flag in the loop
guard.  Synthesis returned `unsat` after 26.5s.

Reading the failure hint surfaced the structural issue: the
framework's per-branch ranking-decrease check fires
unconditionally on every branch, but in the **found** branch
the algorithm doesn't shrink ϕ — it just sets `found := 1`
and lets the AND-guard `lo <= hi AND found == 0` break the
loop.  POPL'10's vacuous-Fpre refinement (Phase 3.J) handles
the analog for recursive calls; the loop version isn't
implemented in this synthesizer.

Claude's first instinct was to **rewrite the algorithm to
match the framework**, not to extend the framework.  Three
attempts:

1. **Case-split τ on `idx`.**  Use `Implies(idx == -1, …)` for
   the search-state atoms (strict-prefix, strict-suffix) and
   `Implies(idx >= 0, …)` for the witness atoms.  Combine with
   a clamped ϕ that drops to 0 once `idx` is set.  Result:
   "valid attribute classes per constraint were found, but no
   Boolean assignment satisfies all of them simultaneously."
   29k checks in 27s.  This failure mode — per-class valid,
   globally inconsistent — was new; banked as Signal 6 in
   `debug.skill`.

2. **Double-weighted ϕ.**  Keep the same case-split τ but use
   `ϕ = (hi - lo + 1) + (1 if idx == -1 else 0)`.  The `+1`
   bonus disappears in the found branch, supplying the strict
   decrease without window collapse.  Same failure mode (29k
   checks, 13s).  Z3 individually satisfies each constraint
   but couldn't compose them.

3. **Three-phase template.**  Restructure the algorithm so the
   loop **always** collapses the window via `<=` / `>`
   comparisons (no early exit, no found-flag), then a
   post-loop `SB(n=2)` checks `A[lo - 1] == x` to decide the
   witness.  Result: VERIFIED in ~30s.

The third attempt is what the synthesizer wanted.  The loop
proper maintains "[0, lo) holds values ≤ x" and "(hi, n) holds
values > x"; after collapse, `lo == hi + 1` and the witness (if
any) lives at `A[lo - 1]`.  This is a classical algorithm
variant — "rightmost binary search" — that happens to fit our
framework's decrease semantics.

**What Claude missed.**  The first two attempts both surfaced
"per-class valid, globally inconsistent" — a hint that the
case-split τ was the problem, not the ϕ.  Claude pattern-
matched on "ϕ doesn't decrease enough" and kept changing ϕ;
the real issue was that no single τ subset could simultaneously
satisfy the inductive at the found branch (which needs
`Implies(idx >= 0, …)` atoms) AND the post (which needs the
strict-prefix/suffix atoms that are `Implies(idx == -1, …)`
gated).  The 3-phase template removed the case-split
entirely.

**What Claude did well.**  After two failed rewrites, instead
of attempting a fourth tweak Claude stopped and asked
"what does the algorithm actually do that exposes our
framework's gap?" — the AND-guarded exit.  That reframing led
to the 3-phase pattern in one try.  Worth banking the pattern
to `problem.skill` (REC 10) so future authors don't repeat
the iteration.

The deeper finding is that **algorithms with multiple distinct
exit signals don't fit our framework cleanly**.  POPL'10's
`SB(n>1)` was designed for branching, not for "this branch
exits the loop without changing ϕ".  Implementing the
vacuous-Fpre refinement for loops would unlock the classical
found-flag pattern; until then, restructuring as init → unconditional
search → post-check is the workaround.

### CS-6.  The helper-axiom strategy for `.solved.lean` curation

Phase X.S surfaced a different shape of curation problem.  Z3
wedged on `modular_exponentiation`'s loop inductive — the
classical fact `result * pow(base, exp) ≡ pow(b, e) (mod m)`
preserved across odd-branch transitions.  The dumped
`.failed.lean` was 16 attribute-class variants; the user
explicitly asked Claude to start curating proofs.

For the easy obligations (initial state, ranking lower-bound,
non-negativity), the proofs were one-liners (`omega`,
`Int.emod_nonneg`, `subst_eqs; rw [one_mul]`).  Five sc0 / sc2
companions landed in under 15 minutes.

The HARD obligation — the modular-product inductive across the
odd branch — needed a fact NOT in the user's stated axioms:
`pow(x % m, k) % m = pow(x, k) % m`.  This is provable from
the given `pow` recurrence axioms by induction on `k`, but the
inline induction is heavy (~30 lines of `Int.induction_on'`
with case analysis on `k = 0` vs successor).

Claude proposed the **helper-axiom strategy**: introduce the
derivable fact as a `private axiom` inside the `.solved.lean`,
with a documenting comment indicating it's derivable from the
user's axioms and should eventually be replaced by an inductive
proof.

```lean
-- Helper: pow respects modular reduction in its first argument.
-- Derivable from user_axiom_0, user_axiom_1, user_axiom_3 by
-- induction on k.  Assumed here to keep the proof tractable; a
-- future revision should prove this from the user's axioms.
private axiom pow_mod_base (x k mm : Int) (hk : k ≥ 0) (hm : mm ≥ 1) :
    (pow (x % mm) k) % mm = (pow x k) % mm
```

The full proof of the hard obligation (~60 lines, using axioms
1, 2, 3 to rewrite `pow base exp` through the odd-exponent
decomposition and `pow_mod_base` to discharge the
modular-reduction step) type-checked first try.

**What this captures.**  The mechanically-checked corpus
distinguishes three states:

- **Z3-proven** (no Lean dump).  The synthesizer dispatched
  the obligation cleanly.
- **Lean-proven from user axioms** (`.solved.lean` with no
  private axioms).  Z3 wedged but the obligation closes from
  the user's axiom set alone.
- **Lean-proven modulo a derivable helper** (`.solved.lean`
  with a `private axiom`).  Z3 wedged, and the user's stated
  axioms alone make the inline proof prohibitively long.
  The helper is documented as derivable.

This third state is **honest**: it makes the dependency
visible.  A reviewer can see the helper, verify the math, and
either accept the companion or replace it.  Crucially, the
helper is `private`, so it doesn't leak out — it's bound to
this one curated proof.

**What Claude did well.**  Proposed the strategy unprompted
after working through the math; named it ("helper-axiom
strategy") and noted it as worth promoting to `problem.skill`.
The proof structure (axiom-rewrite chain through three pow
lemmas + `Int.emod_emod_of_dvd` simplification + axiom 3 in
both directions) was tight on first attempt.

**What Claude missed initially.**  When asking the user to
choose between (a) inline induction and (b) helper axiom, the
implicit question was "is the corpus a proof-of-everything or
a proof-of-the-interesting-parts?".  The user's prior guidance
("mechanically-checked counterexamples beat prose comments")
suggested they want rigor — but rigor doesn't mean every
sub-lemma must be inline.  The helper-axiom approach IS
mechanically checked: `lake env lean` type-checks the whole
file including the axiom declaration.  The `private` qualifier
+ documenting comment is the rigorous version.

This pattern is now banked as `problem.skill` "Helper-axiom
strategy for `.solved.lean` curation".  Expect to see it on
~3-5 hard obligations across the remaining UF-bearing stretch
benchmarks (Kadane's sum-range upper bound, Boyer-Moore's ∀v
count, Floyd-Warshall's `sp` recurrence).

**Curating majority_element exposed a SECOND helper-axiom
mode** (added 2026-05-17 after CS-6's first attempt).  When
attempting Boyer-Moore's loop inductive, Claude realized the
user's stated invariant — `∀v. cnt + count_eq(A, i, candidate)
≥ count_eq(A, i, v)` — does NOT preserve under the branch
transitions using only the supplied count_eq axioms.  Concrete
analysis: when `cnt = 0` and the algorithm adopts a new
candidate, the new invariant requires `count_eq(A, i, A[i]) + 2
≥ count_eq(A, i, v)` for any v ≠ A[i] — and the old invariant
only gives `count_eq(A, i, v) ≤ count_eq(A, i, candidate)`,
which doesn't bound A[i]'s count from below.

The classical Boyer-Moore proof works by tracking "cnt as lead
since last adoption" — an auxiliary quantity NOT expressible as
a single τ-atom in the current IR.  Claude proposed a **Tier 2
helper-axiom**: `bm_inv_preserve_b0` and `bm_inv_preserve_b1`,
which ARE the inductive step itself, stated at the meta level
"the Boyer-Moore invariant preserves under each branch".

This is a stronger trust ask than `pow_mod_base` (Tier 1 —
a derivable local lemma).  Tier 2 effectively says "I trust
Boyer-Moore is correct, modulo this whole-step encapsulation".

The honest framing — banked in `problem.skill` — is that
**when curation forces a Tier-2 helper, that's a signal the
user's τ atoms are too weak to be self-inductive**.  A future
revision should either:
- enrich τ with stronger atoms (e.g., add a ghost
  "cnt-since-adoption" tracking the lead count); OR
- prove the helper via a richer auxiliary invariant in a
  separate Lean file.

For the Phase X.S curation pass, both helpers (Tier 1 + Tier 2)
landed, and all 16 majority_element companions type-check.  The
benchmark is now "Lean-checked modulo Boyer-Moore being a
correct algorithm" — which is a credible claim for a published
1981 algorithm, but is documented as a Tier-2 dependency in
each .solved.lean's docstring.

**What Claude did well (continued).**  When generating 12 of
16 companions that shared a structural template, Claude
escalated to a Python codegen script (`/tmp/majgen.py`) rather
than hand-writing each.  Each variant was a different choice
of which goal conjuncts to prove — 0 ≤ i', i' ≤ n, cnt' ≥ 0,
and the ∀v invariant — and the parameterized template
canonicalized the proof structure.  Banked as
`problem.skill` "Codegen for repetitive proofs".  Lesson
generalizable: if 3+ `.solved.lean` files differ only in
which conjuncts they prove, write a generator.

### CS-7.  Modular exponentiation: the τ-size-vs-enumeration trade-off

`modular_exponentiation` from the Phase X.S corpus produced two
diagnostic runs across one session, each surfacing a different
bottleneck.  Together they expose a structural tension between
**spec correctness** (need enough τ atoms to derive the post)
and **enumeration cost** (each added τ atom doubles per-
constraint subset enumeration).

**Run 1 — 4 τ atoms, 75% cache hits, UNSAT.**

After hand-curating 16 `.solved.lean` companions for the
synthesizer's first-run failure dumps, a 25-minute solo
re-run produced:

> 632 attribute-class checks; Lean fallthrough: 470 valid,
> 64 unknown, 90 error.  valid attribute classes per
> constraint were found, but no Boolean assignment satisfies
> all of them simultaneously.

The 75% cache hit rate validated the helper-axiom strategy at
scale: 470 cached proofs closed their classes in ~3 seconds
each.  But the global SAT still said no consistent τ-subset
choice exists across all constraints.

Claude dug into the `.failed.lean` dumps for the bundle-post
(sc7) and found the root cause: the user's τ atoms include
`result ≥ 0` but **not** `result < m`.  The bundle-post needs
to derive `result' = pow(b, e) % m` from the loop invariant
`(result' * pow(base', exp')) % m = pow(b, e) % m` at exit
(when `exp' = 0`, so `pow(base', 0) = 1`).  That reduces to
`result' % m = pow(b, e) % m`, but the post wants strict
equality.  Need `0 ≤ result' < m` so `result' % m = result'`.

At init `result := 1` violates `result < m` when `m = 1`.  Two
fixes: strengthen pre to `m ≥ 2`, or change init to
`result := 1 % m`.  Claude picked the latter.

**Run 2 — 5 τ atoms, 30-minute timeout, no output.**

With `result < m` added and `result := 1 % m`, the synth ran
30 minutes and timed out without producing output.  The dumps
show why: enumeration didn't reach sc4..sc7.  The synthesizer
wedged in sc3 enumeration — at 2^5 = 32 subsets per
constraint × 8 constraints = ~256 classes, most needing Lean
dispatch at 3-15 seconds each, total wall-clock blew past
the budget.

**The trade-off, formalized.**

The fix WAS correct — `result < m` IS the missing fact.  But
adding τ atoms is monotone-bad for enumeration cost.  More
atoms ⇒ more subsets ⇒ more Lean calls ⇒ more wall time.  At
some point you can't fit the fixed cost (3-15s per Lean call)
× the variable count (2^N subsets) into the wall budget.

**What Claude did well.**  Diagnosed the root cause from a
single failure-dump's goal text, by tracing the proof from
loop-exit τ to the post.  The diagnosis was correct: the
spec gap was real.  Banked the τ-atom-gap diagnostic to
`debug.skill` Signal 6 extension AND the Lean cache hit-rate
metric to Signal 7 — both lessons salvaged from the
investigation even though the benchmark itself stayed xfail.

**What Claude initially missed.**  Didn't anticipate that
adding one atom would 2× enumeration.  Should have estimated
the cost increase before recommending the fix.  Even with
estimating, the right call is still to fix the spec — but
the second bottleneck would have been forecast rather than
surprise.

**Banked as research data.**  `modular_exponentiation` now
serves as the canonical example of the τ-size-vs-enumeration
trade-off.  Two follow-ups in `RESEARCH.md` §B.4:
- Smaller τ via stronger bilateral atoms (single atom
  subsuming `result ≥ 0 ∧ result < m`?  E.g.,
  `result ∈ [0, m)` if our IR encoded interval-membership
  directly).
- Cache-skip optimization (whitelist `.checked` file) so
  cache hits become ~instant instead of 3-5s.

The investigation IS the result.  The benchmark stays xfail
with a detailed XFAIL_REASON pointing future curators at the
two paths forward.

### CS-8.  Codegen as plumbing — the boundary that made it work

**Context.**  Several Phase X.S stretch benchmarks (kadane,
majority_element, modular_exponentiation) timed out at 10-30
minutes despite curated `.solved.lean` companions: the per-call
Lean cost (~30-60s through the generic mathlib tactic chain)
multiplied by the PLDI'09 enumeration count blew past any
reasonable budget.  The Floyd-Warshall benchmark surfaced the
same wall: even with a hand-written Helpers.lean proving the
bundle-post obligation, the generic chain re-derived the proof
from atoms instead of citing the helper.

**My pushback (initial).**  Claude proposed a "codegen module"
that would emit Lean proof bodies from chosen atoms.  I rejected
it as driver-LLM territory — codegen-as-semantic-proof-writer
is exactly the pattern we'd previously committed to keep out of
the synthesizer (and inside an outer LLM loop, if anywhere).

**The reconsideration.**  When per-Lean-call cost became the
dominant bottleneck, Claude reframed.  The actual proposal split
into two: (i) semantic proof writing — REJECTED, still LLM
territory; (ii) structural plumbing — a one-line `exact <helper>
<args>` citation whose argument list is mechanically derived
from the translator's existing signature generation.  Helpers
carry the math; codegen carries the wrapper.  The "rejected"
framing didn't actually cover (ii) because it's exactly what
the translator already does for failed dumps, just citing a
helper instead of trying a tactic chain.

**Resolution.**  Validated E2E across 3 benchmarks.
modular_exponentiation: 30-min timeout → 70s.  kadane: 10-min
timeout → 70s.  majority_element: UNSAT (1487s of wasted
enumeration) → 3 min.  Each ports the same pattern: write a
helper in `Helpers.lean`; register HelperEntry + cite lambda;
synth picks up the fast path automatically.

**What Claude did well.**  Surfaced the boundary distinction
crisply once the cost data was in.  Validated across three
benchmarks (not just FW, which was the easy canary) before
declaring victory.  Noticed within one experiment that routing
`ranking-*` to Lean dispatch caused a 10-min regression on
kadane and modexp — process contention from per-call
`lake env lean` overhead — and reverted the routing.  Banked
the routing allowlist (`_AXIOM_HEAVY_DISPATCH_KINDS`) and the
selective `_on_z3_sat` cross-check as explicit invariants.

**What Claude missed initially.**  Tried to put ranking-* on
Lean dispatch to fix a majority_element UNKNOWN problem.  This
broke the 37s milestone on kadane and modexp.  I had to
remind Claude to "be extra sure we don't lose the 37s
milestone."  In retrospect, the right rule was always there:
linear arithmetic stays on Z3 because Z3 handles it in
milliseconds and Lean dispatch is process-bound at ~3-5s
minimum per call.

**What the result says about the partnership.**  The original
rejection of "codegen as proof writer" was the right
constraint, but it shaded a too-broad ZONE.  Pushing on the
constraint with hard cost data ("the per-call Lean overhead is
where wall-time is going") let Claude carve out a narrower
boundary (structural plumbing, not semantic writing) that
preserved the original intent.  Boundary work is most useful
when the original boundary was drawn ahead of the cost data.

### CS-9.  Floyd-Warshall: from 40-min wedge to <60s via three layered fixes

**Decision point.** With the chain-aware translator landed
(task #167) and 6 Tier-2 helpers wired (sc1, sc2, sc4, sc6,
sc9, sc11, sc13), the user asked Claude to run Floyd-Warshall
E2E synthesis.  Claude expected a successful run in
single-digit minutes.  Instead the run wedged: 33 dumps in 56
minutes wall, all `sc8` (ranking-lb L2) fall-throughs.  The
helpers covered every axiom-heavy obligation, but Claude
hadn't accounted for the `ranking-lb` enumeration cost: τ@L2
has 11 atoms (2^11 = 2048 subsets per `other_assign` combo),
and FW's sc10 has 18 ANT atoms — the Cartesian blowup.

**Evidence that surfaced it.** Process inspection showed
Python at 0% CPU while a single `lean` subprocess pegged a
core at 99% — sequential Lean fallback on Z3-UNKNOWN τ
subsets.  Each Lean call ~5-15s.  At one dump per minute, FW
would take hours.

**Three options surfaced** (Claude proposed; user chose).
(A) cache-only Lean for ranking-*, (B) load-bearing atom
screening, (C) cardinality-ordered enumeration with monotone
pruning.  The user said "#1 first."  Claude implemented A
first (cheap, 14 LOC), validated sum_array still passed,
landed on main.  FW v5 went 30+ min without finishing — the
underlying enumeration cost was still there.

**Branching.** The user said: "lets be explicit about this
note in the branch md ... if it works, and there are no
regressions, we will need to add detailed summary."  Claude
created `experimental/cardinality-ordered-enum` and wrote a
design doc capturing exit criteria (FW <10 min; no
regression; soundness preserved).  Cardinality enum landed
on the branch.  FW v6: <60 seconds, classical 3-loop DP
synthesized correctly.

**The regression surprise.** Quick regression on the
experimental branch showed `insertion_sort` at 417 seconds —
40x its (assumed) baseline.  Claude initially diagnosed it as
"my optimization regressed insertion_sort" and proposed
reverting.  The user pushed back: "investigate why
insertion_sort regressed first."

**The bisection.** Claude ran insertion_sort on main —
**also 412 seconds**.  The regression was pre-existing, not
caused by cardinality enum.  Bisecting commits identified the
real cause: an earlier translator fix (2b164b4, nested chain-
bundle case) had ENABLED translation of a previously-
NotImplementedError-skipped obligation in insertion_sort.
Translation succeeded, generic tactic chain couldn't close,
60+ Lean dispatches per run.

**Resolution.** Two pieces.  (1) A Tier-2 helper for the
nested obligation (`insertion_sort_l1_body_inductive_chain`).
(2) Lifting the §H.2 helper short-circuit out of the axiom-
heavy gating block so it fires for any benchmark with a
helper_registry — insertion_sort isn't axiom-heavy (no UF /
axioms) so the original short-circuit hadn't applied.  After
both: insertion_sort drops to 6.5s.

**What Claude did well.**  After the cache-only attempt
didn't move the needle, Claude correctly identified the
underlying combinatorics and proposed three concrete options
with cost/risk analysis.  The experimental-branch approach
was the user's idea, but Claude internalized it well: writing
the design doc with exit criteria BEFORE coding made the
"revert" decision auditable later.

**What Claude missed initially.**
- **Conflated insertion_sort's main baseline with intuition.**
  Claude assumed insertion_sort was fast on main based on
  pattern recognition (small benchmark, no UF).  In reality
  it was already 412s on main, and Claude had to be told to
  bisect rather than revert.
- **Cardinality optimization first attempt emitted partial
  cubes that broke main SAT.**  intsqrt and sumi returned
  NoSolution because the main SAT layer couldn't compose the
  minimal-only cubes across constraints.  Claude debugged in
  one shot (changed to "leave non-minimal indicators free in
  the cube") but the first iteration would have regressed
  every benchmark.
- **Didn't gate cardinality on τ size initially.**  Without
  the |τ|≥10 gate, sum_array's small-τ ranking-lb went
  through cardinality, each single-atom subset triggered
  expensive UF E-matching, and total time blew up 10x.
  Adding the gate restored sum_array to its (already 100s)
  baseline.

**The cost-data lesson, again.**  The earlier H.2.CODEGEN
case study (CS-8) noted that the original "no codegen"
boundary was redrawn once Claude had hard cost data.  The
cardinality optimization is the same pattern: the previous
boundary ("Phase 3.L monotonicity is the optimization, don't
try further") held because nobody had a benchmark hitting
2^18 ANT subsets.  FW provided that data; with it, the
narrower boundary ("cardinality-ordered for ranking-* with
|τ|≥10, same-position") became visible.  The general rule:
optimizations gated on per-kind structural classification
beat optimizations gated on benchmark-specific hints.

**Lesson for Claude's downstream copilot work.**  When an
optimization breaks a benchmark, the first instinct is "my
change caused the regression."  But on a research codebase
with rapid changes, the regression may pre-date your work.
Bisection against main is cheap (one stash + checkout); doing
it BEFORE reverting saved the cardinality optimization here.

## CS-10: Tier-2-first authoring → IR-level fix two-step (merge Tier-1 push)

**Branch point**: Friday 2026-05-19 evening — merge_two_sorted
sat at 2/7 Tier-1 (only `merge_l1_entry_chain` and
`merge_final_post_chain` proved; the rest were named axioms).
BENCHMARKS.STATUS (then `STRETCH_STATUS.md`) notes called the four per-step helpers
(`merge_branch0/1_preserves_inv`, `merge_l1_drain_b`,
`merge_l2_drain_a`) as promotable with "~80-120 lines per
branch."

The hidden complication: every one of those helpers hits a
boundary case.  After `i' = i+1`, when `i' = n`, the τ atom
`Implies(i+j > 0, C[i+j-1] <= A[i])` requires `C'[i+j] ≤ A[n]`,
but `is_sorted(A, n) = 1` only constrains A[0..n-1].  A[n] is
unconstrained, so the inductive step can't close from user
axioms alone.

**Decision under uncertainty**: Claude's first instinct was
"add 2 focused boundary axioms" (`merge_array_boundary_A/B`:
`is_sorted A n = 1 → A (n-1) ≤ A n`), then prove the 4 helpers
with those axioms in scope.  Net: 4 algorithmic axioms → 4
Tier-1 theorems + 2 one-line focused axioms.  Concrete,
committable progress.  Committed (f975af6).

After committing, Claude re-examined the boundary issue: the
"A[n] is the sentinel" assumption is the **user's caller
contract**, not a mathematical fact.  An IR-level fix would
gate the τ atom on `i<n` (vacuous at boundary), eliminating
the need for the axiom entirely:
```python
"Implies(And(i + j > 0, i < n), C[i + j - 1] <= A[i])"
```

**Surprise**: this fix turned out to also make
`merge_l2_entry_chain`'s 6th conjunct vacuous when
`i_s3 = n_s3` — initially looked like a free additional
promotion.  But on closer analysis, the chain-aware
abstract Loop transition for L1 doesn't preserve C across
the boundary (L1 modifies C; no frame eq), so the
non-vacuous case (`i_s3 < n_s3`) remains unprovable.
Lesson #55 recorded the precision limit.

**Resolution**: two-commit sequence
  - **f975af6**: Tier-2-first with 2 focused boundary axioms
    (intermediate state).
  - **306400b**: IR-level τ gating eliminates the axioms.

Net: merge went 2/7 → 6/7 Tier-1, with 1 genuine ceiling
remaining (precision limit, not promotable without
translator work).

**What Claude did well**:
  - Recognized the boundary case isolated enough to capture
    in 2 one-liner axioms — concrete commit boundary.
  - Re-examined the trust posture after committing: "these
    are caller-contract axioms, not algorithmic; is there a
    cleaner way?"
  - Identified the IR-level fix as a clean second step.
  - When the second step revealed `merge_l2_entry_chain`
    *isn't* fully fixed, traced the actual precision limit
    (abstract Loop transition doesn't preserve C) rather
    than adding more axioms.

**What Claude missed (or paused over)**:
  - Initially over-claimed that the IR-level fix would
    promote `merge_l2_entry_chain` (the 4th merge Tier-2
    axiom).  On closer analysis of the abstract Loop
    transition's frame eq behavior, the ceiling remained.
    The mid-task re-analysis caught the over-claim before
    committing, but a more disciplined "check both
    promotions before claiming wins" pass would have caught
    it earlier.
  - The Tier-2-first → IR-fix path was the second iteration
    in this session; the first iteration ran the 4 helpers
    as Tier-1 with axioms (f975af6) before the IR-fix
    insight.  In retrospect, the IR fix was the cleaner
    target, but the two-step shape gave incremental
    commitable progress.

**General lesson banked (#54)**: Tier-2-first authoring
works even better when boundary cases are isolable as small
focused axioms.  The incremental commit shape is the
underrated benefit — each commit has a cheap exit criterion,
the work can be paused and resumed, and the focused axiom
documents the gap explicitly.

## CS-11: Recognizing when enumeration isn't the right tool (open-problem framing)

**Branch point**: Tuesday 2026-05-20 evening — after the
Tier-1 push, the user asked for "edge of novel algorithm"
benchmark candidates beyond Toom-3 / Karatsuba.  I produced
a catalog (`OPEN_PRBS.md`, 23 items in two layers).  After
some honesty passes (L2.5 / L2.6 SETH-blocked,
L2.10/11/13/14 framework-mismatched and dropped), we
committed to L2.1 (Karatsuba over GF(2^k)) as the prototype
target.

**The first iteration**: I encoded the bilinear-rank
decomposition for GF(2)[x] polynomial multiplication as a
direct Z3 SAT search — boolean variables for the
coefficient choices in each bilinear form, XOR-folded
tensor-equality constraints over the 9 input-pair products.
At n=2 (Karatsuba R=3), n=3 (Cenk-Hasan R=6), and n=4
(R=9), the search settled cleanly: K=K_optimal SAT in
0.1-8.1s, K=K_optimal-1 UNSAT in 0.0-8.1s with symmetry
breaking.  We Z3-kernel-confirmed three known bilinear
rank values.

**The wedge**: at n=5, the direct search hit a wall.  K=9
SAT in 0.7s (the naive bound), but K=8 timed out at 5 min.
Running with longer budgets — 25-min Z3 internal timeout,
30-min shell timeout — produced the same outcome: no
verdict.  At one point a 53-min process had to be manually
killed because the parallel-search threads' internal
timeouts didn't fire reliably (perhaps a bug in Z3's
parallel-search timeout propagation; we didn't dig).

**The user's intervention**: rather than letting me try
yet another encoding trick or larger budget, the user asked
the framing question: *"in addition to a simple Z3
encoding, can we leverage our framework with our Lean
fallbacks to abstract (e.g., higher sizes or problem
subparts) so that we can look for solutions with a mix of
Z3 search and Lean axiomatic proving?"*

The framing matters.  The synthesizer's STRENGTH is
predicate-abstraction reasoning over inductive structures
plus UF axiom routing to Lean — not raw bilinear-rank
search.  Direct SAT enumeration over 2^N decompositions
is what we'd call (in Pragna terms) a "naive search"
strategy; the framework's value-add is in turning bigger
problems into smaller verifications via abstraction.

**My response**: I proposed two complementary strategies:

  (A) **Recursive abstraction via UFs**: treat smaller
      polymul sizes as uninterpreted functions with
      correctness axioms; each UF call counts as one
      "abstract multiplication."  Lean discharges the
      algebraic identity proofs; Z3 handles the linear-
      combination search.  Decouples scaling: leaf size
      via direct Z3 SAT, composition via synth + Lean.

  (B) **Template + predicate search over algebraic
      structure**: treat "evaluate at points → sub-multiply
      → interpolate" as a template; predicates parameterize
      the evaluation points and interpolation matrix.
      PLDI'09 reduction enumerates; Lean verifies polynomial
      identities.

Both strategies leverage the existing UF + recurrence-axiom
path (already used by modexp, sum_array, factorial).
Strategy A is the right tool for "find a recursive scheme
at size n that uses K calls to polymul_k"; Strategy B is
the right tool for "verify a published algorithm at
arbitrary n."

**Resolution**: park the direct search as a negative-result
data point (n=5 K=13 wedge, documented in `karatsuba_gf2/
REPORT.md` §(e)) and prototype Strategy A at n=4 (where
we know R(4)=9) as a smoke test.  If it works, push to n=5.

**What this case study captures**:

1. **Recognizing framework misfit early**.  The Z3 SAT
   search settled n=2/3/4 cleanly because the search spaces
   were tractable.  At n=5 the wedge was a SIGNAL that
   direct enumeration was no longer the right tool — not
   just "Z3 needs more time."  The user spotted this faster
   than I did; I was still in "tune the encoding" mode.

2. **The synthesizer is a verifier first, a searcher
   second**.  Its strength is "given this proposed
   decomposition, prove it correct" — composed with PLDI'09
   reduction over predicate spaces, this gives a search of
   sorts.  But for problems where the SEARCH DIMENSION is
   bilinear-rank-style combinatorial, the existing IR
   doesn't naturally help.  Strategy A converts the
   problem into one where the synth's strengths apply:
   "verify recursive compositions" plus "search over
   recipes."

3. **Multi-strategy framing in a single response**.  After
   the user posed the framing question, the right move was
   to lay out the design space (Strategies A + B), tag
   which regime each wins in, and propose a concrete next
   step (prototype Strategy A at n=4).  Resisting the
   temptation to commit to one approach prematurely.

4. **Negative results are first-class.**  The n=5 K=13
   wedge isn't a failure of the framework — it's evidence
   for why Strategy A is needed.  Documenting it carefully
   in `REPORT.md` §(e) makes the case for the alternative
   compelling.

**What Claude did well**:

  - Built the direct Z3 search cleanly at n=2/3/4 (fast
    iteration, kernel-checked results).
  - Confirmed published bilinear rank values via SAT
    (independent of algebraic-rank arguments).
  - Documented the catalog (`OPEN_PRBS.md`) and
    recharacterized items after deeper assessment (L2.5,
    L2.6 SETH-blocked; L2.10/11/13/14 dropped).
  - When asked the framing question, immediately
    proposed two strategies with regime tables and a
    concrete next step.

**What Claude missed (or was slow on)**:

  - Initially overstated the openness of R(3) over GF(2)
    in `OPEN_PRBS.md`.  Should have done a lit-review pass
    before claiming the n=3 case was open.  Cenk-Hasan 2007
    had settled it.
  - Defaulted to "try a longer Z3 timeout" when n=5 K=13
    wedged, instead of stepping back and asking whether
    the FRAMING was right.  The user had to intervene
    with the framing question.
  - Didn't proactively propose the recursive abstraction
    strategy until prompted.  In retrospect, the modexp /
    sum_array UF axiom path was a natural precedent for
    composing smaller verified pieces, and that should
    have surfaced earlier.

**Lessons banked for future collaboration**:

  - **When a benchmark wedges past expected time, ask if
    enumeration is the right approach**, not just "give it
    more time."
  - **The synth framework is a verifier + searcher hybrid**.
    For pure combinatorial search problems, direct SMT
    encoding may be faster than the synth's PLDI'09
    reduction — but only at small scale.  At larger scale,
    abstraction is the only path.
  - **Negative results document themselves** when the
    research direction shifts.  The wedge IS the case for
    the alternative.

## CS-12: "How are you connecting the cost bounds to actual code?" — declaring completion before checking it

**Branch point**: 2026-05-22, mid-day, in the middle of the
COST_INVS multi-slice landing.  §1 (IR extension) had
landed.  §1.5 (nested-loop composition) had landed.  §2
(Lean cost-composition lemma library + wiring) had landed.
§3 (graph + matching Lean substrate) had landed.  §4 (L1.6
template speculation framework) had landed.  All six slices
shipped clean, CI green, lemma library compiling, the §4
sweep producing the "TGT_TIGHT invalid for all templates"
table.  I wrote up the COST_INVS.md "Status" section
declaring most of the substrate complete and was about to
move to the next research direction.

**The user's question**: *"how are you connecting the cost
bounds to actual code synthesis here?  what i was thinking
was perhaps it could be the case that you can use the §4
framework to verify (1) actual code for a hand-coded
algorithm and (2) speculate over alternatives at the cost
target side."*

**What surfaced**.  The §4 framework I had landed was
working — but only at the LEAN-AXIOM level.  Each entry in
the (template, cost-target) sweep was a Lean theorem
template citing `HopcroftKarpCost` / `GloverIntervalCost` /
`BucketedIntervalCost` as named cost axioms.  The
"templates" were Lean predicates over abstract algorithm
names, NOT control-flow templates in the synthesizer's IR.
There was no actual code being synthesized, no `Loop` / `SB`
/ `Recur` getting filled in, no `cost@L` hole on a real IR
construct.  I had built a clean speculation harness — but it
spoke to the verifier directly, bypassing the synthesizer
that was supposed to be the whole point.

**The pivot**.  Two concrete deliverables, paired:
  - **(1)** Drive ONE cost-bound benchmark end-to-end through
    the actual synthesizer (`Problem` → `expand` → `generate`
    → `solve` → `cost@L` hole filled in with a Lean-verified
    cost expression).  This forces every IR plumbing gap to
    surface.
  - **(2)** Hand-code a Glover-shape matching benchmark with
    cost annotation in the IR, prove it synthesizes (or
    surface the helper requirement and authentic-document it
    as a ceiling).

**Resolution**.  (1) produced
`benchmarks/open_prbs/l16_bipartite_matching/bench_glover_verify.py`,
which synthesizes a cost-bound matching benchmark in the
real IR — `cost@L = n - i` against `cost_target = "n"`, τ
includes `is_valid_pm`, Lean verifies via a Tier-3 helper
citation.  In producing it, I had to admit that the matching
operations themselves are FULLY AXIOMATIZED UFs
(`empty_matching`, `process_endpoint`) — the IR doesn't have
graph or list primitives.  So (1) validated the
cost-invariants pipeline (cost@L holes + cost-lb +
cost-decrement + cost-budget all working end-to-end), but
NOT algorithm discovery — the algorithm was hand-encoded as
axiomatic operations.  (2) landed earlier as a documented
verification failure: the generic Lean tactic chain
(`aesop`, `simp_all`) couldn't instantiate the quantified
UF axioms, requiring the Tier-3 helper that (1) ended up
relying on.

**What this case study captures**:

1. **The "declaring done" failure mode.**  I had a checklist
   in my head (§1, §1.5, §2, §3, §4) and was treating
   completion of each as monotonic progress toward the
   north star.  Each slice in isolation was real progress —
   §3's Lean substrate is genuinely useful infrastructure,
   §4's speculation table is a real artifact.  But the
   composition I'd built was a parallel track to the
   synthesizer, not an integration WITH it.  The user's
   question — "how are you connecting these to code?" — was
   the missing acceptance criterion that the slice-by-slice
   completion checklist didn't surface.

2. **"Driving one benchmark end-to-end" as the integration
   test.**  Before declaring an infrastructure landing done,
   pick ONE concrete consumer and walk it through the entire
   pipeline.  For COST_INVS that's a benchmark file with
   `cost_target` set, running through `solve`, producing a
   `cost@L` hole filled in with a Lean-verified expression.
   If any step is "but in this case the synth wouldn't
   really be doing X, it would be the Lean substrate doing
   it directly," that's the signal that the integration is
   incomplete — even if every individual slice compiled.

3. **Honest characterization of what's axiomatized**.  The
   resulting `bench_glover_verify.py` synthesizes E2E — but
   the matching primitives are UFs with axiomatic semantics.
   In the README and CLAUDE.md I now state this explicitly:
   "the algorithm is FULLY AXIOMATIZED; this validates the
   cost-invariants pipeline, not algorithm discovery."
   Without the user's prompting, I would have shipped a
   weaker characterization ("first cost-bound matching
   benchmark synthesizes end-to-end") that would have read
   as a stronger claim than what was actually delivered.
   Algorithm discovery on graph problems requires a graph
   IR + list/array primitives + new operations — multi-week
   future work — and saying so up front is more honest than
   leaving it as a footnote.

4. **The pattern repeats.**  This is the same case-study
   pattern as the day-10/day-11 Lean fallthrough vs
   sound-by-default story (CS-3 in this report): the
   "improvement" looked real on the slice-by-slice metric,
   but the soundness condition I should have been checking
   was different.  In day-10's case, lenient fallback was
   masking translator bugs.  Here, the §4 framework was
   bypassing the synthesizer.  Both times, the user asked
   the right question and the gap surfaced immediately.

**What Claude did well**:

  - Landed each slice cleanly with CI green between each.
  - Wrote `COST_INVS.md` status updates that accurately
    reflected what shipped slice-by-slice (no inflation).
  - When asked the framing question, responded with two
    paired deliverables (the (1) + (2) split) rather than
    immediately diving in, which let the user signal that
    (1) was the priority.
  - Surfaced the "fully axiomatized" honest framing
    proactively when writing up the bench_glover_verify.py
    deliverable — once the gap was visible, characterized
    it accurately.

**What Claude missed (or was slow on)**:

  - Treated slice completion as project completion.  The
    integration test ("drive ONE benchmark E2E") was not on
    the checklist that the slice plan came from
    (`COST_INVS.md`), and I never added it.  Without the
    user's question, the §1–§4 landing would have been
    declared "done" with a parallel-track speculation
    framework that didn't touch the synthesizer.
  - Slow to recognize the structural similarity to CS-3
    (lenient fallback masking translator bugs).  Same shape
    — slice metrics looked clean, soundness condition
    elsewhere — but I didn't connect the pattern until
    writing this case study.
  - When characterizing limits, I tend to bank them in
    deferred-followup sections of `COST_INVS.md` rather than
    in the README's status paragraph.  Limits relegated to
    follow-up sections feel "managed"; surfaced in the
    headline status, they're load-bearing.

**Lessons banked for future collaboration**:

  - **Add an "integration drive" criterion to every
    multi-slice infrastructure phase.**  Before declaring
    completion, name one downstream consumer that exercises
    the whole pipeline end-to-end.  If the answer is "but
    we don't have a downstream consumer yet," the phase
    isn't done — write the consumer.
  - **Treat the user's framing questions as the integration
    tests Claude didn't write.**  When the user asks "how
    are you connecting X to Y," they're usually pointing at
    a missing integration step.  Don't defend the slice
    metrics; engage the framing.
  - **Honest framing belongs in the headline.**  If the
    deliverable has a load-bearing limitation ("fully
    axiomatized," "test passes only on this input class"),
    surface it in the status paragraph, not in §6 of a
    deferred-followup list.

## CS-13: "Unified SAT vs parallel subprocesses" — when the user's architectural intuition was load-bearing

**Branch point**: 2026-05-23, mid-day, drafting Slice C.  Slice B
had closed; the natural next step was multi-template Cartesian
search (pick among algorithm shapes, not just bodies).  I had
sketched two architectures in a back-of-the-envelope summary:

  - **L0 — light harness**: per-`Problem` subprocesses,
    aggregated.  "Too thin."
  - **L1 — `TemplateUnion` IR node**: a new IR construct that
    `expand()` recognizes; the synthesizer builds ONE
    `ConstraintSystem` with template-indicator gates, and the
    main SAT picks the active template + body atoms in a unified
    search.
  - **L2 — template-shape synthesis**: search over template
    parameters.  "Multi-week research."

I had recommended **L1**, framing it as a clean IR feature with
roughly a week of work.  The recommendation read like the obvious
middle-of-the-road answer between L0 (too thin) and L2 (too
ambitious).

**The user's pushback**: *"Are you suggesting creating a giant
SAT problem with union of the expanded templates?  Or are you
suggesting running multiple sat instances and picking whichever
one gets solved.  The former (single SAT instance with union)
seems like it might create a very difficult SAT instance for
the solver (toplevel union means the solver needs to explore
subfragment on its own); while not providing the benefit of
parallel SAT exploration with parallel solvers running
simultaneously."*

**What surfaced**.  The user identified four specific
breakdowns in Architecture A that I had glossed over:

  1. **No cross-template information to share.**  Templates in
     our IR have different `tau@L*` / `g@L*` / `phi@L*` hole IDs
     (different loop_ids).  They share nothing the SAT solver
     can exploit beyond the pre/post/inputs that are already
     known at problem construction time.  A unified SAT pays
     larger state for no compounding gain.
  2. **SAT discovers disjointness dynamically.**  The solver
     doesn't know a-priori that templates are independent; it
     has to learn that `t_B = True` makes all `t_A`-gated
     clauses vacuous.  Wasted backtracking through
     cross-template combinations.
  3. **PLDI'09 per-class enumeration stays N×.**  Enumeration
     is per-CONSTRAINT, and constraints belong to specific
     templates.  Architecture A batches the enumeration into
     one process but doesn't shrink the work.
  4. **No parallelism.**  Z3 runs single-threaded for SAT.  The
     framework's cleanest speedup dimension — cross-process
     parallelism (which our regression suite already uses for
     Z3 state isolation) — is thrown away.

The fourth point was decisive.  Z3 doesn't parallelize SAT
search internally, and our existing regression infrastructure
already does subprocess isolation for Z3-state safety.
Architecture A would have built a single bigger SAT that ran
serially while the system had N cores available — strictly
worse than running N independent SAT instances in parallel.

**The pivot**.  Switched recommendation to **parallel-subprocess
harness** (~150 LOC orchestration layer, `ProcessPoolExecutor`
with 'spawn').  No IR changes; each template is a complete
`Problem` solved independently.  Result aggregation +
per-variant ranking happens at the harness layer.

**The validation arc**.  Three observations from running the
benchmark:

  - **Smoke benchmark works parallel.**  Two sumi variants
    (count_up, count_down) synth in <100ms each, parallel
    total ~210ms vs serial ~73ms.  Subprocess spawn dominates
    at this scale, but the architecture works.
  - **Real benchmark parallel-mode fails.**  The L1.6
    multi-template benchmark with 3 expensive variants in
    parallel mode returned "no_solution" for templates that
    had working `.solved.lean` helpers.  Diagnosis: 3 synth
    subprocesses × ~4 internal Lean workers each saturated
    the 8-core host; `lake env lean` cache-lookup invocations
    timed out at 15s → spurious unknown verdicts.
  - **Sequential mode works perfectly.**  Same benchmark,
    `max_workers=1`, returns the correct 2-PICK / 1-REJECT
    table.

So the harness has TWO regimes: parallel for cheap variants
(smoke), sequential-via-subprocess for expensive ones.  Same
architecture, switched by a max_workers knob.  Architecture A
couldn't have offered this — it would have been one big
ConstraintSystem with no obvious "step back to serial"
fallback.

**What this case study captures**:

1. **The "obvious middle-of-the-road" recommendation can be
   wrong.**  L1 (`TemplateUnion` IR node) felt right because it
   was between L0 (too thin) and L2 (too ambitious).  But the
   middle option's tradeoffs hadn't been thought through.  When
   Claude generates a 3-level decision matrix, the middle is
   often the path of least intellectual friction — and it
   doesn't get the same critical review as the extremes.

2. **The user's architectural intuition was load-bearing.**  I
   had laid out all four breakdown points in my own L1 sketch
   in different paragraphs, but hadn't connected them into
   "therefore Architecture A is wrong."  The user's question
   ("are you suggesting unified SAT or parallel?")  forced the
   synthesis I should have done before recommending.

3. **The pushback was specific to the architecture, not the
   slice goal.**  The user didn't say "don't do Slice C" or
   "Slice C is wrong."  They said "this specific architecture
   has these specific problems."  The fix preserved every
   slice-C goal — Cartesian template search, exploration
   table, multi-variant verification — but on a substantially
   simpler implementation.

4. **The parallel-contention finding only emerged from
   running it.**  Even after pivoting to Architecture B, the
   harness's failure under heavy concurrent Lean dispatch
   wasn't predicted from first principles; it surfaced from
   running the benchmark.  This wouldn't have surfaced under
   Architecture A at all — the unified SAT would have just
   taken longer, with no observable "cache lookup timed out"
   signal.  Architecture B's failure mode is at least
   diagnosable.

5. **"Run multiple SAT instances and pick whichever gets
   solved" is the right framing.**  The user's phrasing
   foreshadowed a deeper observation: multi-template
   exploration is not "find ONE solution across all
   templates"; it's "find a solution per template that
   admits one."  Architecture A treats templates as
   alternatives in a single search.  Architecture B treats
   them as independent problems — same problem class, different
   parameters.  The latter framing matches what the user
   actually wants out of the exploration: a TABLE, not a
   winner.

**Lesson banked (RESEARCH.md §I, lesson #61)**: *Multi-template
should NOT be unified-SAT.*  The intuition "let the SAT
solver search jointly over algorithm shapes" is wrong for our
IR.  When multi-shape exploration becomes desirable, the
right architecture is an orchestration layer that runs N
independent `solve()` calls in parallel — never a single SAT
covering the union.

## Cross-cutting observations

> Update as patterns emerge across case studies.

- **Claude is reactive, not proactive about soundness.**  When
  told "this is a soundness improvement", Claude implements it
  well.  When discovering a soundness gap in passing, Claude
  often documents it ("worth noting", "this could be unsound")
  rather than escalating to the user for direction.  The
  `potentially_unsound = True` flag we live with on axiom-heavy
  benchmarks is partly because Claude accepted "lenient by
  default" early without flagging that it masks bugs.
- **Self-correction speed is good.**  When the user pushes back
  with a specific principle ("counterexamples should be
  mechanically checked", "Z3 SAT on axiom-heavy is suspect"),
  Claude integrates the new constraint immediately and propagates
  it through subsequent decisions.
- **Multi-phase context retention is the differentiator.**  CLAUDE.md
  + `MEMORY.md` + skill files act as a compressed project memory.
  Without them, every session would start cold.  The discipline of
  banking encoding lessons (45+ to date) is what makes Claude
  feel like a continuous collaborator rather than a series of
  one-shot consultations.

## Methodology notes

- Phase Y.2 corpus is the long-term play; the short-term value of
  Claude is per-phase implementation + the discipline of writing
  things down.
- The expr-report (this file) is updated whenever a case study
  surfaces.  Keep entries concrete: decision point, evidence,
  resolution, what Claude did, what Claude missed.
- Don't pad.  If a phase was uneventful, no case study is needed.


## CS-14: "Lean says VALID, but is that the obligation Z3 was asked?" — cross-side parity bugs hide in plain sight

**Branch point**: 2026-05-24, mid-day, K.D ("chain-aware
break") had just landed.  I was implementing the abstract
Loop transition for break-capable Loops on the Z3 side:
when a Loop's body has a `_break` branch, the loop can exit
early with `g` still true, so we drop `¬g` from the abstract
transition (only `τ_inner` + frame eqs remain).  This was
the right Z3-side change.

I ran the 2-loop K.3.2 benchmark to validate.  It synthesized
in 578s — first L1.6 nested-loop benchmark with break + flip.
Several hours' work, end-to-end-validated.  Shipped.

**What I missed**.  The Lean translator's
`_emit_chain_item_hyps` was UNCHANGED by my Z3-side fix.  It
still emitted `h_i1_L1_not_g : ¬ g_L1(s2)` as a hypothesis
for every Loop in the chain — regardless of break-capability.

This meant: Lean theorems for chain-bundle-post obligations
had a STRONGER hypothesis set than the Z3 constraints they
were supposed to mirror.  Lean could prove obligations from
`(τ ∧ ¬g)` that Z3's actual `τ` alone couldn't establish.

If Lean validates, the framework records the class as
VALID.  Main SAT picks a cube depending on that validity.
The emitted code's correctness relies on the Z3 obligation
holding — which it might not, if Lean only proved the
stronger form.

**The discovery**.  Reading 3-loop sc7 failure dumps the
next day (for the 3-nested K.3.2 push), I noticed
`h_i1_L1_not_g` in the binder list.  But L1 was break-capable
— the Z3 side had dropped that hypothesis from its abstract
trans.  Where was this coming from?

`grep _emit_chain_item_hyps` revealed the parallel emission
in `translate.py` that I hadn't touched.  The fix was
mechanical: gate the `_not_g` binder emission on
`_has_break_branch(item.body, problem)`.

**Soundness audit**.  Did any of the K.3.2 2-loop's earlier
"success" rely on the over-validation?  Re-ran the benchmark
with the fix.  Same 578s, same verified solution.  The over-
validation hadn't actually fired in a load-bearing way —
because the per-class validation cubes happened to be
inclusive enough that the weaker Z3 obligation also held.
But that's luck, not correctness.

**What this case study captures**:

1. **Cross-side parity bugs are silent.**  The unsoundness
   doesn't show up as a crash, a failed test, or a "wrong"
   verdict.  It shows up as "the system might emit unsound
   code on a benchmark we haven't run yet."  Defending
   against it requires explicitly auditing parity whenever
   the Z3 side changes.

2. **The translator and the constraint generator must be
   mirror images.**  Every change to which hypotheses Z3
   includes (or excludes) for a construct needs the
   parallel change in the Lean translator.  Mismatch =
   unsoundness, even when each side individually looks
   correct.

3. **What I did well**.  I read the failure dumps when
   debugging the 3-nested benchmark — and the parity issue
   surfaced naturally in that reading.  Banking lesson #66
   so future framework work has the parity-audit checklist
   explicit.

4. **What I missed**.  I should have audited the translator
   when the Z3-side abstract trans changed.  The fact that
   it landed on main with this gap for ~24 hours is
   uncomfortable.  Mitigation: add an automated parity
   check as part of the test suite (compare translator's
   hypothesis names against the Z3 constraint's structural
   shape).  Banked as future work.

---

## CS-15: "Should we have a timeout?" — the user's question that turned a 3-hour wedge into a 30-second signal

**Branch point**: 2026-05-25, 4 AM (per the user's transcript
log).  The 3-nested K.3.2 benchmark had been running for 3+
hours.  I had launched it expecting ~30 min.  No output, no
sign of progress.  CPU showed Lean processes spawning and
finishing, but the synth wasn't returning.

The user, presumably noticing the long-running process,
interrupted with: *"it has been running for 3 hours. is that
expected?"*

I checked.  Found 83 sc7 failure dumps in the dump directory
— the L0 body-inductive constraint had been enumerating
τ-subsets and Lean was rejecting all of them.  Each rejection
took ~5s.  Per-constraint enumeration was burning through
hundreds of subsets serially, finding NONE valid.

**The diagnostic gap**.  From the user's perspective: the
synth was running.  No output.  Was it 5 minutes from done?
Was it stuck?  No way to tell.  The wedge had been silently
in progress for 3 hours.

I killed the run, diagnosed the missing helper, added it,
re-ran.  Closed in 1466s.

**The user's question that mattered**.  After we landed
3-nested, the user asked: *"should we have a timeout in the
framework that triggers which gives us a signal that a lean
call is wedging and we need to write a tier-3 helper?"*

This was the right question.  My instinct on the 3-hour
wedge had been "investigate the specific constraint, fix the
helper, move on."  The user reframed: this is a CLASS of
problem (any future benchmark could wedge similarly), and
the right response is INFRASTRUCTURE that makes wedges
visible.

**The design that followed**.

  - Per-constraint Lean dispatch counter.
  - At `wedge_threshold` non-valid dispatches (default 30):
    print one-line `[WEDGE]` warning naming the constraint
    + a sample dump path.
  - At `2 × wedge_threshold`: ABANDON enumeration on that
    constraint, cancel queued futures via
    `executor.shutdown(cancel_futures=True)`, mark as
    needs-helper.
  - At end-of-run: return `NoSolution(reason="needs-helpers")`
    with a hint listing each wedged constraint's tuple
    (kind, loop_id, branch_idx, sample dump).

**Validation**.  Re-ran the K.3.2 2-loop benchmark with
helpers disabled and `wedge_threshold=10`.  Four wedges
surfaced cleanly in 830s; the final NoSolution explicitly
named sc1, sc3, sc7, sc9 with their tuples + dump paths.
The diagnostic that would have saved 3 hours yesterday now
fires inside minutes.

**Validation #2**.  On the very NEXT benchmark (3-nested
K.3.2), I had proactively authored 5 helpers but missed
sc1.  The wedge detector caught it on the first run (60
dispatches, ABANDON, NEEDS-HELPERS hint pointing straight
at sc1).  Helper added; second run closed in 1466s.

**What this case study captures**:

1. **The user's reframing was the load-bearing move.**  My
   instinct had been "fix this specific wedge."  The user's
   "should we have a timeout" question lifted the response
   one level: the wedge wasn't a one-off; the LACK OF SIGNAL
   was the durable problem.  Infrastructure that makes
   wedges visible saves hours on every future benchmark.

2. **Cheap diagnostics compound.**  ~120 LOC of solver
   instrumentation, default-on, configurable per `Problem`.
   Cost: trivial.  Benefit: every future benchmark that hits
   a wedge gets a clear failure mode + actionable hint
   instead of a silent multi-hour grind.

3. **The 3-nested validation was the proof.**  The wedge
   detector's first real use case caught a missing helper
   I had genuinely overlooked.  This is the kind of feedback
   loop that makes infrastructure investments pay back fast.

4. **What I did well**.  The implementation included future
   cancellation (`executor.shutdown(wait=False,
   cancel_futures=True)`) so in-flight Lean dispatches
   don't keep grinding after abandonment.  That detail
   matters at scale.

---

## CS-16: "How are you measuring this?" — performance optimization is full of regressions you didn't think about

**Branch point**: 2026-05-25, mid-morning, K.D + wedge
detector had landed.  The user asked about timing
optimization given K.3.2 timings: 1-loop 403s, 2-loop 578s,
3-loop 1466s.  3-loop with flip 2851s.  Tractable but slow.

I proposed three optimizations: trivial-helper auto-
generation (~2× wall), expanded Z3 trust list (~1.5×),
distributed Lean resolver cluster (architectural, big swing).

The user picked auto-helpers and asked me to log the cluster
architecture for future work.

**Implementation arc**.  Three slices:

  - **Slice 1** (`coverage` only): emit `subst_eqs + omega`
    proofs for branch-coverage obligations.  Validated on
    1-loop: 403s → 346s (1.16×).  Modest but real.

  - **Slice 2** (widen to safety-bundle-entry/post + safety):
    add `obtain ⟨_, _, ...⟩ := h_pre` destructuring + multi-
    arity `refine` fallback chain.  Tested per-class:
    coverage at 1.4s, entry at 2.2s, post at 2.3s (Core-only,
    no mathlib).  Validated on 2-loop: 578s → 325s (1.78×).
    On 3-loop: 1466s → 554s (2.65×).  Scaling looked great.

  - **Slice 3** (regression check): ran the broader
    benchmark suite.  Two issues surfaced.

**Issue 1 — `array_zero` regressed 6s → 46s.**  The auto-
template was firing on array_zero's safety obligations.
The conclusion didn't mention `store`, so my bailout check
let it through.  But the trans hypothesis was
`h_trans_A : A' = store A i 0` — auto-template's
`subst_eqs + omega` couldn't unfold the store, so it failed
all 2^4 τ subsets, falling back to generic chain.  Per
subset: 1.4s wasted + 4.5s generic = 5.9s vs just-generic's
4.5s.  Net regression on every store-of-trans benchmark.

Fix: bail out of auto-template if `store ` or `store2d `
appears ANYWHERE in the theorem text — including in
trans/frame hypotheses, not just the conclusion.  Trivial
one-line patch.  array_zero went 46s → 42s (back to noise
of the baseline 39.9s).

**Issue 2 — sc9 wedge on 2-loop with auto-helpers on.**
The auto-template was triggering on L0 final-bundle
obligations for the 2-loop benchmark.  Some subsets
validated; some didn't.  The wedge detector fired on the
ones that didn't — paid the 1.4s × 60 dispatches before
abandoning.

This was a real wedge — the auto-template can't handle the
chain through Loop_L0 fully.  But the benchmark still
synthesized: enough subsets validated before abandonment to
construct a global solution.  No fix needed; the wedge
detector's signal is informational, not a synth-failure.

**What this case study captures**:

1. **Performance work surfaces regressions you didn't
   anticipate.**  The auto-template was designed around
   K.3.2-family shapes.  array_zero is a totally different
   shape (in-place array modification, no quantified MI).
   The auto-template's "bail out on store in conclusion"
   check was right but incomplete; "anywhere in theorem"
   was the real rule.

2. **Conservative widening + bailout is the right pattern.**
   The auto-template only fires on KNOWN shapes (coverage,
   safety-bundle-entry, etc.) AND only when no store
   appears.  False positives waste ~1.4s; false negatives
   (auto-template doesn't fire when it could) fall back to
   the generic chain.  Asymmetric costs: false-positive
   regressions are immediate and surface-able (regression
   suite); false-negatives are invisible (just slower than
   they could be).  Bias toward conservative.

3. **The Z3 trust list expansion (option 2) was rejected
   after soundness review.**  Initially I had recommended
   it as a ~1.5× quick win.  The user asked for the
   soundness review before implementation.  Two failure
   modes surfaced: (a) Z3's E-matching can miss quantifier
   instances under user axioms → spurious UNSAT → spurious
   VALID; (b) Z3's quantified-array reasoning is unsound on
   K.3.2-family shapes (lesson #65, the dummy-axiom trip-
   wire).  Safe expansion would need per-OBLIGATION quantifier-
   free check, which buys little on the K.3.2-family.
   Skipped.

4. **What I did well**.  The user's "before we embark, can
   we do a review" framing for the Z3 trust list was load-
   bearing.  Without it, I would have implemented the
   expansion, re-introduced the K.3.2 unsoundness, and the
   wedge detector would have masked it (looking like a
   correctness issue rather than a soundness one).
   Surfaced this in the soundness review document; rejected
   the optimization with documented reasoning.

5. **What I missed**.  My initial perf numbers (1.16× /
   1.78× / 2.65×) sounded great until I ran the broader
   regression.  I should have run array_zero BEFORE
   claiming the speedup; I assumed K.3.2-family numbers
   would generalize.  Mitigation: every perf claim should
   carry a regression-suite validation, not just hot-path
   measurements.

---

## CS-17: Slice 2.B's hidden framework bug — a generator-vs-mutation atom_refs trap

**Branch point**: Slice 2.B (max matching with axiomatized
Berge) had nine Tier-3 helpers, each individually validated
via `verify_class_via_lean`.  But synth wedged at 445s; the
wedge detector abandoned sc14, one of the two Cartesian chain
paths through the final SB(n=2).  Two facts looked
contradictory: (a) a direct smoke test on the sc14 helper —
same chosen atoms the solver would pick — returned
`status=valid, via_helper=True, 4.28s`.  (b) During real
synth, the helper short-circuit never fired on sc14; the
solver fell back to per-subset enumeration, every subset
went UNKNOWN, and the wedge detector abandoned the
constraint.  If the helper validates in isolation, why
doesn't the solver use it?

**The misleading hypothesis**.  My first guess: the two
Cartesian paths (sc13 = recur branch, sc14 = identity
branch) have indistinguishable `applies_to` signatures —
both are `kind=safety-bundle-post, loop_id=L0,
branch_idx=None`.  Maybe the solver was emitting conflicting
branch indicators across the two paths, blocking global
SAT.  I documented this as a hypothesis to test in
`SLICE_2B_STATUS.md`.  It felt plausible.  It was also
wrong, and I spent ~30 minutes pursuing it before stepping
back.

**The diagnostic that worked**.  A focused script comparing
sc13's and sc14's attributes — kind, loop_id, branch_idx,
and atom_refs count — surfaced the real signal: sc13 had
4 atom_refs, sc14 had **0**.  Downstream, the helper
short-circuit gates on `_extract_loop_id(sc) is not None`,
which (when `sc.loop_id` is None) falls back to scanning
atom_refs.  With zero refs, that returned None, and the
short-circuit silently skipped sc14.  The helper was
configured, the cite type-checked, the smoke test passed —
but the solver never tried to use it.

**Root cause** (~10 lines in `constraints.py`).
`chain_paths_local` is a Python generator.  Before yielding
paths, it builds `per_item` for the chain — including a
single `tau_at()` call for the Loop's abstract transition
that appends 4 atom_refs to the per-constraint accumulator
`current_refs`.  Then it yields N Cartesian paths via
`itertools.product`.  Each yielded path becomes a
`SafetyConstraint` via `commit()`, which captures
`current_refs` and **clears** it.  The first commit grabs
the 4 refs.  Every subsequent commit captures empty.  Fix:
snapshot the refs accumulated during `per_item` build;
restore the snapshot per yielded iteration so every commit
captures the same set.  Verified: sc14 atom_refs went 0 →
4, helper short-circuit fired, and a 445s wedge collapsed to
117s.

**The aftershock**.  117s still UNSATed.  Helper coverage
had jumped from 4.3% to 38.1%, but 11 attribute-class
UNKNOWNs were still being rejected under sound mode.
Solver-side instrumentation revealed two further issues:
3 ranking-lb subsets where Z3 UNKNOWNed under UF-axiom
interactions, and 8 sc15 procedure-level coverage subsets
that the solver gate excluded from Lean dispatch (Lean
was never tried).  Fixes: carve out `coverage` kind in the
Lean-dispatch gate (a separate `fix/*` commit), and rewrite
`mm_sc15_coverage`'s `required_atoms` to demand only the
one load-bearing τ atom so per-subset enumeration could
still fire the helper on partial subsets.  Final result:
102s, 1 verified solution.

**What I did well**.  Three things.  First, when I
hypothesized the cube-conflict scenario, I wrote it into
the status doc as a hypothesis-to-test, not as the answer
— so when atom_refs=0 surfaced, I could swap explanations
cleanly without backtracking through claims.  Second, I
wrote the smoke test BEFORE chasing the wedge.  The
"isolation works but integration doesn't" gap was the
load-bearing signal; without that signal I'd have assumed
the helper itself was broken and been hunting in the wrong
place.  Third, after the framework fix landed and synth
closed at 117s, I did NOT declare victory — recognized that
11 UNKNOWNs remained, instrumented the solver, and surfaced
the procedure-level coverage gap as a separate fix.

**What I missed**.  The cube-conflict hypothesis cost ~30
minutes that a more disciplined "diff sc13 and sc14
systematically" probe FIRST would have saved.  Pattern-
matching on plausibility ("indistinguishable applies_to
signatures!") came before mechanical comparison ("just
print every field side-by-side").  Mechanical first, then
hypothesis.  Separately: I tried `potentially_unsound=True`
to bypass the lingering UNKNOWNs without first checking
that the production code path for that flag had been
excised — would have grep'd the flag's actual usage if I'd
paused.  And on the helper-narrowing attempt, I tried
`required_atoms={2,3}` for sc14 before reading that the
cite was hard-coded for 4 positional args.  Trial-and-error
before understanding, twice in one session.

**Cross-cutting reflection**.  Framework bugs hide behind
benchmark-level "issues."  My instinct was to assume Slice
2.B was missing a helper or had a τ-design problem — a
benchmark-level fix.  The smoke-test-vs-actual-run
discrepancy was what redirected attention upstream.  When
isolation works but integration doesn't, the bug is in the
integration layer, not the unit.  This is the third time
this project has banked a framework bug surfaced by a
specific benchmark wedging (cf. lessons #29 / #30 / #66).
Worth treating "this benchmark behaves weirdly even though
its parts look right" as a framework-level smell going
forward, not a benchmark-level smell.

## CS-18: Slice 2.C — from 5 axioms to 2 by proving the flip-preserves-matching theorem in Lean

**Branch point**.  Slice 2.B (CS-17) shipped max matching
with axiomatized Berge plus four algorithm-specific axioms
(MatchingSize bounds, flip-increases-size, flip-preserves-
IsMatching, class-restriction).  This left a soundness gap:
"we trust five properties of the algorithm; only Berge is a
classical theorem; the other four are about THIS particular
flip operation."  The user proposed Thread A — keep Berge
axiomatic, but replace the algorithm-specific axioms with
concrete predicate definitions plus Lean proofs.  Discussed
before any code moved, scoped to flip-preserves-IsMatching
as the load-bearing one.

**The discovery in scratch**.  A first proof attempt in
`scratch/2c_flip_proof.lean` revealed that the natural 3-atom
IsMatching predicate (range + symmetric + edge) is
INSUFFICIENT.  Without the no-self-loop atom (`M[k] ≠ k`),
the case analysis breaks: the {u, v, z = M[v], w}
distinctness argument fails when `M[v] = v` is allowed,
which the 3-atom predicate permits but a real matching does
not.  Added a fourth atom.  Banked as lesson #73 — UF
predicates often have hidden assumptions that only surface
when you go concrete and try to prove something.

**The proof**.  `flip_preserves_im` is ~120 LOC of real
Lean.  Establishes z := M[v] has range, M[z] = v (symmetric),
z ≠ u (else M[u] = v ≠ -1, contradicting the AP
precondition's `M[u] = -1`), z ≠ v (no-self), z ≠ w (AP
precondition).  For each of 4 conjuncts × 5 cases
(`kk ∈ {u, v, z, w, otherwise}`), unfolds stores or applies
M's atoms.  The "otherwise" case for the symmetric conjunct
requires showing `M[kk] ∉ {u, v, z, w}` via four mini-
contradictions using `M_symm` plus matchedness facts from
the AP precondition.  Not deep math, but real proof
engineering — the kind of step-by-step case analysis that
needs to be iterated in scratch (per CLAUDE.md guidance)
rather than authored in one shot.

**The signature-mismatch surprise**.  After the Tier-1 proof
landed and eight Tier-3 helpers were written, synth wedged
on sc1 (L0 entry).  Direct `verify_class_via_lean` smoke
returned `status=valid`.  Inspection of the failure dump
showed the framework was emitting a FLAT theorem (bare
parameter names) while my helper signature used the chain-
aware shape (`n_s0` / `n_s1`).  Lesson #74 banked: helper
dispatch picks FLAT vs chain-aware based on chain-prefix
structure, and mismatches surface only at synth-time as
`unknown identifier` errors.  After fixing sc1's signature
shape and sc6's guard hypothesis name, v6 synth closed in
131.9s, 1 verified solution.

**Comparison**.  Slice 2.B's synthesized loop invariants
displayed `IsMatching(G, n, M) == 1` — opaque.  Slice 2.C's
invariants display the FOUR concrete `ForAll(kk: ... → ...)`
atoms in plain text.  Axiom count dropped from 5 to 2 (Berge
remains axiomatic; one MatchingSize bound remains for the
ranking argument).  UF count dropped from 4 to 2.

**What I did well**.  Got the Tier-1 proof working in
scratch FIRST (per CLAUDE.md guidance), iterating
`simp [store, ...]` and `by_cases kk = u/v/z/w` until each
case closed before porting.  Discovered the fourth atom
requirement DURING the proof attempt — the proof obligation
forced the predicate definition to tighten, rather than
guessing the predicate upfront.  Identified the FLAT-vs-
chain-aware dispatch issue via failure-dump inspection (the
`exact mm_sc1_l0_entry n_s0 ...` cite in the dump made the
shape mismatch obvious).

**What I missed**.  Wrote all eight helpers in one batch
WITHOUT smoke-testing each, which led to several signature
mismatches surfacing serially during synth.  The better
workflow — smoke-test EACH helper immediately after writing
it — would have caught sc1's FLAT/chain-aware mismatch in
under a minute instead of after a wedged synth run.
Separately, the first helper for sc1 used the chain-aware
shape because Slice 2.B's sc2 helper used it; I should have
looked at the actual chain-prefix structure for L0 vs L1
before picking a shape.  And the bench's class-restriction
axiom shipped with a paren imbalance that crashed the
parser — `ast.parse`-validating axiom strings before running
synth would be trivial insurance.

**Cross-cutting reflection**.  Slice 2.C is the cleanest
demonstration so far of "what does it actually take to
remove an axiom?"  The axiom IS a five-line claim; the
proof is ~120 lines.  The 24× ratio is real and indicative.
For benchmarks where the algorithm-specific axiom encodes
a classical published theorem (like Berge), the pragma
should be to KEEP the axiom — replacing it is multi-day
Lean work for no algorithmic-discovery benefit.  For
algorithm-specific axioms that encode a property of THIS
particular operation (flip-preserves-matching), proving
them in Lean is tractable AND meaningfully shrinks the
trust surface.  Picking the right ones to prove is a
judgement call worth making explicit.

## CS-19: A worked example — `interval_greedy` end-to-end

It's easy to lose sight of what the framework actually
*produces* when each session is about closing one obligation
or extending one translator.  This case study is a bird's-eye
view of one benchmark, end-to-end: input spec → synthesized
code in three languages → mechanically-checked proof
artifacts.  The benchmark is `bench_interval_greedy.py`
(closed 2026-05-27, ~45s wall, 1 verified solution), the
first of the L1.6 BREADTH trio.

**Input — the 75-line spec**.  Given `n` intervals
`[S[i], E[i])` sorted by end-time, find the maximum number of
pairwise non-overlapping intervals.  The user authors a
`Problem` with: template `SB() >> Loop(SB(n=2))` (init then a
loop with a 2-branch body); pre (sorted end-times + valid
intervals); post `count == GreedyCount(S, E, n)`; and the
candidate atoms for each hole.  Crucially, the user does
**not** write the algorithm — they write its specification.
Two UFs (`GreedyCount`, `GreedyLastEnd`) encode the recursive
definition of what greedy EDF produces; six axioms describe
the accept-step / skip-step transitions.  Five candidate τ
atoms, two candidate guards, two candidate transitions.

**Output — three compilable languages**.  In about 45
seconds, the synthesizer picks the right atoms and emits the
algorithm.  Python (default — proof as comments):

```python
def synth(S: list[int], E: list[int], n: int) -> int:
    count = 0; i = 0; last_end = 0
    i, count, last_end = 0, 0, 0 - 1
    # invariant L0: (0 <= i) and (i <= n) and (0 <= count) and
    #               (count == GreedyCount(S, E, i)) and
    #               (last_end == GreedyLastEnd(S, E, i))
    # ranking   L0: n - i
    while i < n:
        if S[i] >= last_end:
            last_end, count, i = E[i], count + 1, i + 1
        elif S[i] < last_end:
            i = i + 1
    return count
```

C (compiles under `clang -Wall -Werror`):

```c
int synth(int *S, int *E, int n) {
    int i = 0, last_end = 0, count = 0;
    i = 0; count = 0; last_end = 0 - 1;
    while (i < n) {
        if (S[i] >= last_end) {
            int __t_last_end = E[i], __t_count = count + 1, __t_i = i + 1;
            last_end = __t_last_end; count = __t_count; i = __t_i;
        } else if (S[i] < last_end) {
            i = i + 1;
        }
    }
    return count;
}
```

Rust (compiles under `rustc -O`):

```rust
pub fn synth(S: &[i64], E: &[i64], n: i64) -> i64 {
    let mut i: i64 = 0; let mut last_end: i64 = 0; let mut count: i64 = 0;
    i = 0; count = 0; last_end = 0 - 1;
    while i < n {
        if S[(i) as usize] >= last_end {
            let __t_last_end: i64 = E[(i) as usize];
            let __t_count: i64 = count + 1;
            let __t_i: i64 = i + 1;
            last_end = __t_last_end; count = __t_count; i = __t_i;
        } else if S[(i) as usize] < last_end {
            i = i + 1;
        }
    }
    count
}
```

Plus a fourth "Python with runtime checks" mode that lowers
every proof obligation to a Python assertion executed on real
inputs — so the synthesizer's static proof and the runtime
behavior are cross-checkable artifact-by-artifact.

**Proof artifacts — 8 obligations + 5 Tier-1 Lean theorems**.
The synthesizer emits 8 safety constraints for this template:
`safety-bundle-entry` (init holds the invariant), `coverage`
(branches cover the loop guard), two `safety` (loop body
inductive — one per branch), two `ranking-decrease` (one per
branch), `ranking-lb` (ranking is non-negative), and
`safety-bundle-post` (exit state implies the post-condition).
The two ranking-* constraints + the lower-bound are pure
linear arithmetic — Z3 closes them in milliseconds.  The
other five obligations route through Lean via Tier-1 helpers
that cite the user-supplied axioms.  A representative example
— `is_sc_accept`, the loop body's accept branch:

```lean
theorem is_sc_accept :
    ∀ (S E : Int → Int) (n count i last_end : Int)
      (count' i' last_end' : Int),
    (n ≥ 0 ∧ … sorted … ∧ … valid …) →
    0 ≤ i → i ≤ n → 0 ≤ count →
    count = GreedyCount S E i →
    last_end = GreedyLastEnd S E i →
    (i < n ∧ S i ≥ last_end) →
    last_end' = E i → count' = count + 1 → i' = i + 1 →
    (0 ≤ i') ∧ (i' ≤ n) ∧ (0 ≤ count') ∧
    (count' = GreedyCount S E i') ∧
    (last_end' = GreedyLastEnd S E i') := by
  intros S E n count i last_end count' i' last_end'
         h_pre h_tau_0 h_tau_1 h_tau_2 h_tau_3 h_tau_4
         h_guard h_trans_last_end h_trans_count h_trans_i
  obtain ⟨h_g_in, h_g_cond⟩ := h_guard
  subst h_trans_i h_trans_count h_trans_last_end
  have h_accept : i ≥ 0 ∧ S i ≥ GreedyLastEnd S E i := by
    refine ⟨h_tau_0, ?_⟩; rw [← h_tau_4]; exact h_g_cond
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · have := greedy_accept_count S E i h_accept; omega
  · have := greedy_accept_last_end S E i h_accept; omega
```

The proof is hand-written once in `Helpers.lean`; the
synthesizer cites it via `exact is_sc_accept …` in the
auto-generated theorem text for the obligation, and Lean's
kernel checks the citation.  The other four helpers
(`is_sc_entry_l0`, `is_sc_coverage`, `is_sc_skip`,
`is_sc_final`) follow the same shape — destructure the
hypotheses, cite the right axiom, close with `omega`.  Each
is 10-25 LOC.

**What this means concretely**.  The total trust surface for
this benchmark is: Z3's QF-LIA decision procedure, Lean's
kernel + `omega`, the six axioms A1-A3 the user declared
(which IS the algorithm's specification, recursively
defined), and ~80 lines of hand-written Lean proof tactics.
The trust surface does NOT include: the algorithm's
control-flow choice (which branch goes where), the branch
guards, the transition expressions in each branch, the loop
invariant, the ranking function, or the initial state.  All
of those were searched.  Of those searched, every choice the
synthesizer committed to is justified by a discharged proof
obligation.

**What Claude did well**.  Designing the spec was a real
research step — encoding "the algorithm matches the
recursive greedy definition" as a UF + step-axioms is a
reusable pattern (analogous to how Slice 2.B handled Berge).
Picking five Tier-1 helpers that each map to one constraint
made the proof structure transparent — when a helper failed
its smoke test, the cause was always either a translator
hypothesis name mismatch or a goal shape mismatch.

**What Claude missed**.  The first cite for `is_sc_coverage`
referenced `h_guard` but the translator names the loop guard
`h_g_loop` — surfaced as an `unknown identifier` error at
synth time, then was a one-line fix.  And the first cite for
`is_sc_accept` listed the three transition hypotheses in the
wrong order (`h_trans_count h_trans_i h_trans_last_end`),
whereas the translator emits them alphabetically by RHS
variable (`h_trans_last_end h_trans_count h_trans_i`).
Smoke-testing each helper individually before launching
synth would catch both in seconds; doing so eventually
became the workflow but only after the run wedged.

**Cross-cutting reflection**.  The artifact this framework
produces is not "code" and it is not "a proof"; it is the
*correlated pair* — code annotated with proof obligations,
each obligation typed as a Lean theorem with a hand-written
or auto-generated proof, the whole thing reproducible from a
75-line spec.  Comparing the spec to the emitted Rust
function is the cleanest way to see what got searched: every
expression in the Rust that does not appear in the spec was
chosen by the solver and justified by a discharged
obligation.  Benchmarks like `interval_greedy` are
qualitatively different from "the synthesizer found a
solution" — they are evidence that the synthesizer can
*explain why* its solution is correct, at a level of
precision a human reviewer can audit.
