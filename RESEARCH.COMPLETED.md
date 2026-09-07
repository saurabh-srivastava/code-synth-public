# RESEARCH.COMPLETED.md

Completed research design passes — kept for the design-
decision archive but no longer load-bearing for active
work.  Moved here from `RESEARCH.md` 2026-06-07 as part of
the doc reconcile.

When citing from active docs, point to the section by name
(e.g., `RESEARCH.COMPLETED.md §K.B`).

---

## §K.B. Break primitive — design pass

**Per the §L principle** (framework over single-case), C1.D
K.3.2's length-3 AP detection is pursued via Option B: extend
the IR with a `break` primitive for early loop exit.  This
section is the implementation reference.

### K.B.1 Encoding decision

**Encode `break` as a TRANSITION-ATOM FLAG, not a new IR
node.**  An SB-branch transition atom may carry the marker
`"_break": True`:

```python
"s@B1.0": [{"M": "Update(...)", "_break": True}],  # flip + break
"s@B1.1": [{"i": "i + 1"}],                         # continue
```

Why piggyback on atoms rather than introduce `Break()` as an
IR node:
  - Atoms are already framework-aware (`_recur` precedent in
    Phase 3.E).
  - Constraint generation sees atoms one at a time; adding a
    flag check is a local edit.
  - The decoder/emitter already iterate over atoms when
    pretty-printing branches; appending `break;` after the
    branch is mechanical.
  - No `Seq`/`Recur` interaction concerns: break only makes
    sense inside an SB inside a Loop, which is already
    representable.

### K.B.2 Semantics

A break-marked atom in an SB branch inside `Loop(body)`
causes:
  - The branch's transition is applied normally.
  - **Immediately after**, control exits the enclosing
    `Loop` — the post-loop state is the state after the
    transition.
  - The loop's normal-exit case (¬g) is unchanged; break
    is an ADDITIONAL exit path.

Each Loop now has up to N+1 exit paths:
  - 1 normal-exit (¬g, takes the state at iteration head).
  - N break-exits, one per break-marked branch in the body
    (takes the state after that branch's transition).

### K.B.3 Constraint generation changes

For each Loop with break-marked branches in its body:

**(a) Loop inductive (safety) — modify**:
  For break-marked branches, **SKIP** the τ-preservation
  obligation.  The normal "τ ∧ g ∧ trans ⇒ τ'" only applies
  when control loops back; on break we exit, so τ' doesn't
  need to hold at the next iteration.

**(b) Ranking-decrease — modify**:
  For break-marked branches, **SKIP** the ranking-decrease
  obligation.  No further iterations after break.

**(c) Post-bundle (safety-bundle-post) — extend**:
  Currently: one obligation per Loop, of shape
  `bundle ∧ τ ∧ ¬g ⇒ next-state-pre`.

  With break: ADD one obligation per break-marked branch:
  `bundle ∧ τ ∧ g_branch ∧ trans_branch ⇒ next-state-pre`,
  where the state on the LHS is the state AFTER the branch's
  transition.

  Both kinds of post-bundle must hold; main SAT enumerates
  per-class for both.

**(d) Entry-bundle, ranking-lb, coverage** — unchanged.
  These obligations apply to the Loop's structure
  independently of break.

### K.B.4 Translator changes

  - `theorem_for_safety_inductive`: emit τ-preservation
    only for non-break branches.  Same for
    `theorem_for_ranking_decrease`.
  - `theorem_for_chain_bundle` and `_chain_bundle_chain`:
    generate one theorem per exit path.  For the
    framework's `dump_lean_failures_dir`, name them
    `sc<N>_post_bundle_<exit_idx>` where exit_idx is 0
    for ¬g and 1..N for break branches.
  - Tier-3 helper signature-hash filenames extend
    accordingly.

### K.B.5 Decoder + emitters

  - Decoder: when pretty-printing an SB branch whose atom
    has `_break: True`, append `break` after the branch's
    transition.
  - emit_py: emit `break` Python keyword.
  - emit_c: emit `break;` C keyword.
  - emit_rust: emit `break;` Rust keyword.

The framework's existing branch-emission code already
appends `else if` / `else` chains; the `break` keyword goes
inside the branch body before the closing brace.

### K.B.6 Smoke benchmark

Before tackling K.3.2, validate the primitive on a trivial
benchmark — `bench_break_smoke.py`:

```python
inputs = [Var("n", "int", "input"), Var("threshold", "int", "input")]
outputs = [Var("result", "int", "output")]
locals = [Var("i", "int", "local")]
pre = "n >= 0 and threshold >= 0"
post = "(result == -1 or result < n) and (result == -1 or 2*result >= threshold)"

template = SB() >> Loop(SB(n=2)) >> SB()

atoms = {
    "s@B0": [{"i": "0", "result": "0 - 1"}],
    "tau@L0": [
        "0 <= i", "i <= n", "result == -1",
    ],
    "g@L0":   ["i < n"],
    "phi@L0": ["n - i"],
    # Branch 0: 2*i >= threshold — found.  Set result, break.
    "g@B1.0": ["2 * i >= threshold"],
    "s@B1.0": [{"result": "i", "_break": True}],
    # Branch 1: not yet — increment.
    "g@B1.1": ["2 * i < threshold"],
    "s@B1.1": [{"i": "i + 1"}],
    # Post-loop SB: identity.
    "s@B2": [{}],
}
```

Synth picks the right combination; post holds either via:
  - Normal exit (i = n, result stays -1) — case `result == -1`.
  - Break exit (2*i ≥ threshold, result = i) — case `2*result ≥ threshold`.

If this smoke synthesizes, the primitive works.

### K.B.7 Edge cases to handle (or document as out-of-scope)

  - **Break inside nested loops**: only breaks the
    INNERMOST.  No "break N levels" support.  K.3.2 may
    need this; document if so.
  - **Break in non-loop SB**: invalid — only meaningful
    inside a Loop body.  Framework should raise during
    expand if encountered outside a Loop.
  - **All branches break**: degenerate — the loop runs
    at most one iteration.  Allowed; equivalent to a
    no-loop template, but the framework shouldn't crash.
  - **Branch with `_break: True` AND `_recur: True`**:
    invalid combination.  Raise during expand.

### K.B.8 Implementation phases for this session

Conservative scope:
  1. **K.B.IMPL-1** — atom-flag recognition in
     `_trans_body` + branch-walk (~30 LOC).
  2. **K.B.IMPL-2** — skip τ-preservation and
     ranking-decrease for break-marked branches in
     `_emit_loop_body` and `_emit_sb_constraints`
     (~50 LOC).
  3. **K.B.IMPL-3** — extra post-bundle obligation in
     `_emit_chain_bundle` (~60 LOC).
  4. **K.B.IMPL-4** — translator changes (per K.B.4)
     (~80 LOC).
  5. **K.B.IMPL-5** — decoder + emit_py break keyword
     (~30 LOC).
  6. **K.B.IMPL-6** — smoke benchmark (per K.B.6) + run
     (~50 LOC).

Each sub-phase a focused commit.  Validate at each step
(unit-level: parsing works; semantic: smoke synth produces
correct solution).

emit_c + emit_rust break keyword can land in a later
sub-phase once the Python path is working.


## §K.B-REVIEW. Break primitive design review

**Performed 2026-05-24** on a fresh branch
(`c1d/break-primitive`).  Pulls on each §K.B decision asking
"what could go wrong?" before any code lands.

### Issues found and resolutions

**(R1) Atom-flag vs IR node: kept atom-flag, but with caveats.**

§K.B.1 chose atom-flag (`{"_break": True}` inside a transition)
over an `IRNode Break()`.  Trade-offs:

  Pro atom-flag: 1 precedent (`_recur` from Phase 3.E); local
  constraint-generator edit; no expand-walker plumbing across
  Seq/Recur.

  Con atom-flag: less discoverable (a typo `"_braek"` is
  silently treated as a normal field); can't statically reject
  break outside a Loop without an explicit pre-check.

  **Resolution**: stay atom-flag for K.3.2 scope.  Add an
  EXPLICIT validation pass in `expand()` that walks every
  atom and (a) rejects `_break: True` outside a Loop body, (b)
  rejects unknown leading-underscore keys (catches typos).

**(R2) Multi-break SB enumeration cost.**

§K.B.2 allows ≥ 1 break-marked branch per SB(n>1).  Each
break-branch adds a post-bundle obligation.  For SB(n=3) with
2 break-branches, that's 2+1 = 3 post-bundle obligations per
Loop.  Per-class enumeration scales accordingly.

  **Resolution**: fine in practice (K.3.2 uses SB(n=2) with
  1 break-branch; +1 obligation).  Document the scaling for
  future authors but don't gate.

**(R3) Multi-level break: not designed, intentionally.**

§K.B.7 documents single-level only.  K.3.2 with nested-loop
search NEEDS multi-level break in the natural encoding
(break out of inner v-loop AND outer u-loop on flip).

  **Resolution**: the K.3.2 algorithm can be restructured to
  use SINGLE-level break + a post-inner-loop guard that
  recognizes the flip and prevents further outer iterations.
  Concretely:
  ```
  while exists_l3_ap:
      u := 0
      while u < n:
          if M[u] == -1:
              v := 0
              while v < n:
                  if conditions: flip M; break  // single-level
                  v := v + 1
              // u-loop continues; next iteration of u-loop:
              // if M[u] is now non-(-1), the if M[u]==-1 is false → skip
          u := u + 1
  ```
  After the inner break, M[u] is matched, so the u-loop's
  "if M[u] == -1" guard prevents further work for that u.
  Continues over remaining u's.  Equivalent to "restart from
  top" because any new u in range gets checked under the
  current M.

  Multi-level break can land later if needed (e.g., for
  Hopcroft-Karp's BFS phase termination).  Out of scope for
  this branch.

**(R4) τ-preservation skip is correct iff body_out's state is
the LAST one before exit.**

The design says: for break branches, skip the τ-preservation
obligation `τ(body_in) ∧ g ∧ branch ∧ trans ⇒ τ(body_out)`.
Justification: we EXIT after the transition; body_out isn't
the head of a NEXT iteration, so τ at body_out doesn't matter
for soundness.

But: τ(body_out) ALSO appears in any subsequent obligation
that uses the loop's post-state as antecedent (e.g., the
chain-bundle for `Loop >> SB`).  If we skip the τ-preservation,
the framework can't ASSUME τ(body_out) when proving the
post-loop bundle.

  **Resolution**: this is FINE.  The break-bundle obligation
  ALSO doesn't assume τ(body_out) on its LHS — the LHS is
  `bundle ∧ τ(body_in) ∧ g(body_in) ∧ branch ∧ trans`.  The
  framework derives whatever it needs at body_out from
  trans + body_in.  No τ assumption needed.

  Sanity-check: the ¬g case has τ(body_in) AND ¬g; with the
  body's frame eqs, what state is the loop "exiting to"?
  Looking at the chain-aware translator, the answer is "body_in
  + frame eqs."  So the framework already handles "exit at
  body_in" cases via frame.  Break exits at body_out, which
  is body_in + trans — strictly more constrained.  OK.

**(R5) The ranking-decrease skip: also need ranking-lb to
work at body_in.**

§K.B.3(b) skips ranking-decrease for break branches.  Concern:
if the loop is allowed to exit early via break, but the
non-break branches don't decrease ranking properly, the loop
could spin forever.

  **Resolution**: false alarm.  Ranking-decrease is per-branch.
  Non-break branches MUST decrease; break branches are exit
  paths, so no decrease needed.  Ranking-lb still ensures
  phi ≥ 0 at every τ-consistent state (including body-entry).

  But there's a subtle question: can ranking-lb HOLD if break
  is the only way to exit a loop that would otherwise diverge?
  E.g., `while true do break-if-cond`.  The guard is `true`,
  so ¬g never holds.  Ranking-lb says τ ⇒ phi ≥ 0.  Ranking-
  decrease says τ ∧ ¬break ⇒ phi(in) > phi(out).  If the
  loop runs while phi ≥ 0 and decreases per non-break iter,
  it terminates either by phi hitting 0 (contradicts ranking-
  decrease → forces break) or by break firing.  Sound.

  K.3.2 doesn't have a `true` guard; the loop's guard is
  `exists_l3_ap`, so termination comes from exhausting APs.

**(R6) Chain-aware translator must dispatch per-exit-path.**

The chain-aware translator (Phase #167) builds per-state
binders across a chain.  For a Loop with N break-branches +
¬g, the translator must emit N+1 theorems, each with the
loop's exit state being different.

  **Resolution**: the existing `emit_bundle_to` function
  parametrizes on `target_state`.  We add N+1 calls per Loop —
  one for ¬g (existing), N for break branches (new, with
  target_state = body_out of the branch).  Mechanical.

**(R7) Helper signature-hash naming with multiple post-bundles
per Loop.**

Current convention: `sc<N>_fallthrough_<H>.solved.lean` where
`N` is the constraint INDEX.  With multiple post-bundles per
Loop, constraint indices will shift.  Existing benchmark
helpers (e.g., `bench_aug_path_max.py`'s sc4) won't break
because they don't have break — but the indexing scheme
allows new Loops with break to produce more sc-indices.

  **Resolution**: no change needed.  Constraint indices are
  per-system, not per-Loop.  New constraints (break-bundles)
  add new sc indices alphabetically; the framework's dump
  filenames stay content-addressable via signature hash.

**(R8) The smoke benchmark in §K.B.6 IS sound.**

Walked through manually:
  - τ = `{0 ≤ i, i ≤ n, result == -1}`.
  - Branch 0 (2*i ≥ threshold): sets result := i, breaks.
    body_out state: i unchanged, result = i ≠ -1.  τ's
    `result == -1` does NOT hold at body_out, BUT we skip τ-
    preservation for break branches, so OK.
  - Branch 1 (2*i < threshold): i += 1, result unchanged.
    body_out: i+1, result = -1.  τ holds at body_out.
  - Post: `(result == -1 or result < n) and (result == -1 or
    2*result >= threshold)`.
    ¬g case (i = n, result = -1): satisfies via `result == -1`.
    Break case (2*i ≥ threshold, result = i): satisfies via
    `2*result >= threshold ∧ result < n` (latter from `i ≤ n`
    plus `i < n` from `g`).

  Sound.  Both exit paths satisfy post; framework should
  synthesize 1 solution.

**(R9) Tier-3 helpers needed for the smoke benchmark — likely 1.**

Post-bundle for the break path:
`bundle ∧ τ(body_in) ∧ g(body_in) ∧ g_branch_0 ∧ trans_branch_0
  ⇒ POST(body_out)`.

The post `(result == -1 or ...) ∧ (result == -1 or 2*result
  >= threshold)` needs to be derived from `result = i` and
`2*i >= threshold` (branch guard).  Linear arithmetic;
omega/aesop should close.

Post-bundle for the ¬g path: `result == -1` straight from τ.
Aesop.

So smoke likely closes with NO Tier-3 helpers.  Good
acceptance signal.

**(R10) emit_c / emit_rust break keyword interactions.**

`break` in C / Rust exits the IMMEDIATE enclosing loop.  Our
encoding (one-level break out of nearest Loop) matches.  No
deep emitter changes — just append `break;` inside the branch.

For emit_py: `break` is a statement.  Append after the
branch's assignments.

  **Resolution**: trivial emitter work.

### Net design verdict

**Sound.**  No fundamental issues found.  Atom-flag encoding
with (R1)'s validation pass + single-level break + ¬g and
break paths as separate post-bundle obligations gives a
clean primitive.

### Refinements for implementation (vs original §K.B)

Add to §K.B.IMPL-1:
  - **(R1)** Validate at expand time: `_break: True` only in
    atoms inside a Loop body; reject unknown `_<key>` prefixes.

Update §K.B.IMPL-3:
  - **(R6)** Re-use `emit_bundle_to` with N+1 different
    target_states; no new translator function needed.

Out-of-scope flags (R3):
  - Multi-level break.
  - Break inside Recur.

These can be addressed later if the use case appears.

### Confidence

This is the cleanest design pass I've done on a framework
primitive.  The §L principle (framework over single-case) is
applicable: the primitive's cost (~5–7 days) amortizes across
K.3.2-4, Hopcroft-Karp, BFS/DFS search-style algorithms,
and any future "find-first-then-stop" use case.

Ready for implementation.


## §K.D. Chain-aware break — design pass for full K.3.2

**Recorded 2026-05-24** as the next framework extension for
the L1.6 push.  The K.B `break` primitive works for top-level
Loops; full K.3.2's nested-loop AP search needs break to work
when the breaking Loop is INSIDE another Loop or chain.

### K.D.1 The gap

`theorem_for_break_bundle` currently emits:
```
Fpre ∧ τ(body_in) ∧ g(body_in) ∧ branch_guard ∧ trans
    ⇒ Fpost(body_out)
```

For a top-level Loop, `Fpost(body_out)` is the right target —
the break exits the function with body_out as the final state.

For an inner Loop, body_out is NOT Fpost; it's some intermediate
state that flows through the rest of the chain (e.g., the outer
Loop's body's continuation after the inner Loop).

### K.D.2 Two flavors of chain-aware break

  **(K.D.2.a) Break in a Loop inside a CHAIN** (e.g.,
  `Loop_outer >> SB_finalize`):
  After the inner Loop's break, control flows through the
  remaining chain items.  The break's target state must
  satisfy the rest-of-chain's expectations.

  For a chain `SB_init >> Loop_inner >> SB_finalize`, the
  break of Loop_inner exits to body_out, which then flows
  through SB_finalize.  The post-Loop_inner state is the
  state after SB_finalize.  This is what the framework's
  `emit_bundle_to` chain logic already handles for the
  ¬g exit; we just need a SECOND target_state for the break
  exit.

  **(K.D.2.b) Break in a Loop nested inside another Loop**
  (e.g., `Loop_outer(... Loop_inner(... break ...) ...)`):
  After the inner break, control returns to Loop_outer's
  body (the iteration that contained Loop_inner).  Loop_outer
  continues normally — its body inductive obligation applies.

  This case is more complex.  The chain-aware translator
  emits "body inductive" obligations for nested Loops as
  τ_enclosing-preservation theorems.  For the break path, the
  obligation becomes: "if Loop_inner's break fires, the
  enclosing Loop's body still preserves τ_enclosing."

### K.D.3 Scope decision — handle K.D.2.b only

K.3.2 needs K.D.2.b (nested Loop with break in inner).
The simplest design: add a `theorem_for_break_bundle_chain`
that:
  - Takes the same args as `theorem_for_chain_bundle_chain`.
  - Threads the chain state binders.
  - For the target Loop, instead of using its abstract
    transition (τ_inner ∧ ¬g_inner ∧ frame_eqs), use its
    BREAK transition: τ_inner ∧ g_inner ∧ branch_guard ∧
    branch_trans.
  - The goal: τ_enclosing at the post-Loop state (same as
    the normal chain case for nested).

### K.D.4 Constraint generation changes

Currently `emit_loop_body`'s break path emits a constraint
with `Fpost(body_out)` as the consequent.  For nested Loops
(when there's an enclosing loop), the consequent should be
τ_enclosing at the appropriate state instead.

The fix: detect if the Loop is nested (use the same logic
that `theorem_for_chain_bundle_chain` uses to detect
enclosing_loop_id).  If nested, target τ_enclosing-at-body-out
instead of Fpost.

For chain-without-nested (K.D.2.a): the target is Fpost at
the END of the chain (after subsequent items run).  The
break's body_out flows through subsequent SBs.  Need to
either:
  - Pre-compute the final state after running subsequent
    chain items from body_out.  Threading.
  - Or emit a different obligation shape: "body_out
    satisfies the entry condition of the next chain item;
    that item's obligations + ... ⇒ Fpost."

The first approach is simpler.

### K.D.5 Implementation phases

  **K.D.IMPL-1**: detect Loop's enclosing context in
  `emit_loop_body`'s break path.  Use `_linearize_path` or
  similar.

  **K.D.IMPL-2**: emit appropriate break-bundle consequent
  per context:
    - Top-level: Fpost (existing).
    - In chain (no enclosing Loop): Fpost at state-after-
      remaining-chain.
    - Nested (enclosing Loop): τ_enclosing at body_out.

  **K.D.IMPL-3**: extend the translator dispatch
  (`verify.py`) — when `branch_idx != None` AND there's
  a chain prefix or enclosing Loop, dispatch to a new
  `theorem_for_break_bundle_chain`.

  **K.D.IMPL-4**: implement `theorem_for_break_bundle_chain`
  modeled on `theorem_for_chain_bundle_chain` but with the
  break's transition replacing the Loop's abstract ¬g exit.

  **K.D.IMPL-5**: smoke benchmark — nested Loop with break
  in inner (e.g., `find_first_match.py`: two nested loops
  scanning a 2D grid, break on found).

  **K.D.IMPL-6**: K.3.2 proper — three nested loops over
  (u, v, w) for AP search.

### K.D.6 Risks

  - **R-K.D.1**: the chain target state for break is
    different from ¬g.  Need careful per-state-binder
    naming so the Lean translator emits a coherent
    sequence.
  - **R-K.D.2**: the chain prefix's frame eqs may need
    different handling for break — variables modified by
    the Loop's break-transition need to be primed
    consistently with the chain's overall threading.
  - **R-K.D.3**: per-class enumeration cost.  Each Loop
    with break adds N+1 obligations (one per exit path).
    For nested Loops with breaks at multiple levels, the
    count multiplies.

Estimated effort: 3-5 days of framework work + 2-3 days
for K.3.2 helpers afterward.

### K.D.7 Stopping criterion

The smoke benchmark in K.D.IMPL-5 is the acceptance test:
nested Loop with break in inner, synthesizes E2E.  After
that, K.3.2 is benchmark-level work (helpers + iteration)
rather than framework work.

### K.D.8 What landed (2026-05-24)

**K.D.IMPL-1 through IMPL-5 DONE** on branch
`c1d/chain-aware-break`, commit `b347fdd`.

Changes:

  - `constraints.py:emit_loop_body` break path uses
    `enclosing_loop_id` (already plumbed through
    `walk_template` for COST_INVS §1.5) to pick consequent:
    top-level → `Fpost(body_out)`; nested → `τ_enclosing
    (body_out)`.
  - `constraints.py:_has_break_branch` new helper detects
    break-capable Loops; the abstract Loop transition drops
    `¬g_out` when the body has a direct break.  Crucially,
    the helper does NOT recurse into nested Loops — an
    inner Loop's break exits the inner Loop only.
  - `translate.py:theorem_for_break_bundle` takes optional
    `enclosing_loop_id`; conclusion is τ_enclosing
    conjunction (primed for transitioned vars) when set.
  - `verify.py` dispatches via `_linearize_path` to find
    enclosing context.

**Smoke benchmark** `bench_nested_break_smoke.py`:
synthesizes in 0.3s.

**Encoding lesson learned during K.D.IMPL-5**: the
recursive `walk_template` call (from `emit_loop_body`'s
non-SB-body path) uses `pre_fn = τ_outer ∧ g_outer` — NOT
`Fpre`.  Inner constraints in nested-loop benchmarks can
ONLY rely on what `τ_outer` carries.  If `τ_outer` doesn't
include `n_inner ≥ 0` (or other "live" pre facts not
modified by outer body), inner entry-bundle obligations
referencing those facts will UNSAT.  Either carry the fact
in outer τ or restructure.  Lesson candidate for CLAUDE.md.

**Deferred (originally)**:

  - **K.D.2.a** (break in Loop inside a chain with a
    non-empty tail after the Loop) — the inner-break exit
    state isn't the chain target state; would need chain-
    tail composition between `body_out` and the consequent
    check.  Not load-bearing for K.3.2's natural shape
    where inner is the last item.
  - **K.D.IMPL-6**: K.3.2 proper.

### K.D.9 K.D.IMPL-6 landed: K.3.2 2-loop AP search (2026-05-25)

**Commit `ae95e8d` — `bench_aug3_two_loops.py`.**  First
L1.6 benchmark to perform CONCRETE 2-nested-loop
augmenting-path search using nested loops + `break` + the
`found`-flag idiom for outer short-circuiting.  578s wall,
1 verified solution, 3 Tier-3 helpers.

#### Two additional framework improvements banked here

**(i) Fpre propagated into recursive `walk_template`**
(`constraints.py:emit_loop_body`'s non-SB-body recursive
call).  The recursive walk's `pre_fn` is now
`Fpre ∧ τ_outer ∧ g_outer` instead of just
`τ_outer ∧ g_outer`.  Pre facts about input vars are
immutable, so this is sound.  Trims outer τ on
bench_aug3_two_loops from 7 atoms to 3 atoms.

**(ii) Chain-aware Lean translator drops `¬g` for
break-capable Loops** (`translate.py:_emit_chain_item_hyps`,
Loop branch).  Parallel to the Z3-side K.D fix in
`constraints.py`.  This closes a soundness gap where Lean
had more hypotheses than Z3 — Lean could over-validate.

Both are "always-on" framework changes that benefit every
benchmark with nested loops or break-capable Loops, not
just K.3.2.

#### Find-flag idiom (lesson #67)

The synthesized algorithm uses the standard "search nested,
exit on hit" pattern:

```
v, w, found := -1, 0, 0
while (v + 1 < n and found == 0):     -- outer guard short-circuit
    v, w := v + 1, 0                  -- increment-at-start
    while (w < n):
        if AP_conditions:
            found := 1
            break                     -- exits inner only
        else:
            w := w + 1
return M, found
```

The `break` primitive only exits the innermost loop.  To
short-circuit remaining outer iterations, the inner-break
branch sets a `found` flag, and each outer loop's guard
includes `found == 0`.  Combined with the "increment-at-
start" pattern (counters init to `-1`, incremented in the
enclosing body's prep SB), every inner Loop is the LAST
item in its enclosing body chain — so the break's
consequent `τ_enclosing(body_out)` is exact (no K.D.2.a
chain-tail needed).

This unlocks every K-style "search nested + exit on hit"
algorithm within the existing IR.  No new primitive
required beyond `_break`.

#### Still deferred

  - **K.D.2.a** (chain-tail after break) — not needed under
    the find-flag idiom.  Banked.
  - **K.3.2 full 3-nested** (u, v, w all iterated) —
    **DONE 2026-05-25** (commit `1f5a34f`).  See §K.D.10
    below for the landing narrative.
  - **MI-preserving flip** — extending the 2-loop / 3-loop
    search to actually FLIP M and prove matching-invariant
    preserved.  Needs a Tier-3 helper that captures "AP flip
    preserves MI" (case-split on k ∈ {u, v, z, w} vs not).
    No framework gap; pure proof engineering on the helper.

### K.D.W Per-constraint wedge detector (2026-05-25)

`Problem.wedge_threshold: int | None = 30` (new IR field).
The solver tracks per-constraint Lean dispatch outcomes (non-
valid only); two thresholds fire diagnostics:

  - **WARN at `wedge_threshold`**: one-time message identifying
    the wedging constraint by `(kind, loop_id, branch_idx)` and
    pointing at the failure-dump path.
  - **ABANDON at `2 × wedge_threshold`**: stop enumeration on
    that constraint; cancel queued futures via
    `ThreadPoolExecutor.shutdown(wait=False, cancel_futures=True)`;
    in-flight futures drain.

End-of-run: if any constraints abandoned, return
`NoSolution(reason="needs-helpers")` with hints enumerating
the wedged constraints + sample dump paths.

**Validated** on `bench_aug3_two_loops` with
`helper_registry=None` + `wedge_threshold=10`: all 4 wedge-prone
constraints surface, clean `needs-helpers` verdict in 830s.
Default threshold 30 is calibrated so axiom-heavy benchmarks
(fib distributes hundreds of dispatches across many constraints,
~tens per) don't false-flag.

**Soundness** (SOUNDNESS.md): abandoned constraints contribute
empty-or-partial valid-cubes lists; the main SAT UNSATs them;
the synth returns a sound `NoSolution`, never an unverified
solution.

Cost ~120 LOC across `solver.py` + `ir.py`.  Benefit:
every future benchmark gets a clean fast-fail when a constraint
needs help, instead of a silent multi-hour wedge.

### K.D.10 K.3.2 full 3-nested-loop AP search lands (2026-05-25)

**Commit `1f5a34f` — `bench_aug3_three_loops.py`.**  First
CONCRETE 3-nested-loop augmenting-path search to synthesize via
the framework (u, v, w all iterated).  1466s wall, 1 verified
solution, 6 Tier-3 helpers in
`lean/SynthLean/Y2Corpus/l16_aug3_three_loops/Helpers.lean`:
`k32_3l_middle_entry` (sc1), `k32_3l_inner_entry` (sc2),
`k32_3l_inner_break` (sc4), `k32_3l_middle_body_ind` (sc8),
`k32_3l_outer_body_ind` (sc10), `k32_3l_final` (sc12 — FLAT-
shape signature; see lesson #69).

The wedge detector caught a missing sc1 helper on the first run
(60 dispatches before abandonment; `NEEDS-HELPERS` hint pointed
straight at it).  The second run with the added helper closed
in 1466s.  This validates the K.D framework primitive on
3-nested depth and confirms the find-flag idiom (K.D.9
lesson #67) scales beyond 2-nested.

**Sharp edge (lesson #69)**: at L0 level the chain-bundle-post
dispatch in `verify.py` routes to `theorem_for_chain_bundle`
(FLAT — pre-loop vars unprimed, post-loop primed) rather than
`theorem_for_chain_bundle_chain` when the L0 chain prefix has
no non-SB items.  Helper `k32_3l_final` had to be reshaped from
chain-aware `_sN` binders to FLAT (pre/post) before the cite
type-checked.  Banked in problem.skill helper-authoring
section.

---

