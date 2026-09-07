# Community-validation backlog — banked friction findings

**Purpose:** consolidate friction findings from the
community-validation rounds (v1–v8) that were **diagnosed but
not shipped** — either as docs additions or as code fixes.
Each entry below has had its premise **empirically verified**
(see "Verification" line); false positives, speculative
items, and items already covered by existing docs have been
deleted.

**Triage rule (since v6):** ship docs only when verified
necessary by a fresh-agent failure.  v5+v6+v7+v8 = 12/12
agents verified without these fixes, so the rule held.

**Source rounds and outcomes:**

| Round | Prep F-fix | Audit findings (banked) | Audit findings (deleted) |
| --- | --- | --- | --- |
| v1 → v2 | F1–F5 shipped | — | — |
| v2 → v3 | F6+F7+F9 shipped (F8 rejected) | — | — |
| v3 → v4 | F10+F11+F12 shipped | — | — |
| v5 → v6 | F13–F20 shipped | — | — |
| v6 audit | — | F21, F22, F23, F25, F26, F27 | F24 (cardinality overstated) |
| v7 → v8 | F28 shipped | — | — |
| v7 audit | — | F29, F31, F32 | F30 (Lean-tutorial knowledge, not synth) |
| v8 audit | — | F33, F34, F35, F37, F38 | F36 (already covered in REC 11.8 + Core docstring) |
| v8 re-triage | — | — | V8-RT-1, V8-RT-2 (both agent misreadings); F39 (main-agent over-extrapolation) |

**Headline: 14 banked items**, all premise-verified.  Two
audit passes (2026-06-09) deleted 6 entries: 3 confirmed
false positives (V8-RT-1, V8-RT-2, F24), 2 already-covered
docs (F30, F36), 1 main-agent over-extrapolation (F39).

**Cross-cutting meta-finding (2026-06-09)**: of 20 items
originally banked across v6–v8 audits, 6 (30%) did not
survive verification.  The triage rule is doing real work —
without re-checking, ~30% of "obvious-sounding" backlog
items would have triggered fixes for non-problems.

---

## Banked from v6 audit

Source: v6 Q1 (`count_two_arrays_equal`), v6 Q3
(`sum_two_passes`).  All 3/3 verified, findings are
friction-reducers not blockers.

### F21 — `python -c` vs `python script.py` sys.path asymmetry

When a worktree contains a `synth/` directory (i.e. the
repo source tree, present in every `git worktree`),
Python's `-c` invocation puts CWD as `sys.path[0]`,
shadowing the canonical editable install.
`synth.lean_backend.verify._LEAN_DIR` then resolves to a
broken worktree lean dir.  `python script.py` puts
`script.py`'s dir as `sys.path[0]` instead, so the
editable install resolves correctly.

**Verification (2026-06-09):** reproduced empirically.
Fresh `/tmp/v6f21-test/synth/__init__.py` with `FAKE =
'worktree-synth'`:
```
$ python -c "import synth; print(synth.__file__)"
/private/tmp/v6f21-test/synth/__init__.py
$ python -c "import synth; print(synth.FAKE)"
worktree-synth
```
Confirmed asymmetry.

- **Cost when hit**: ~10 min diagnostic time (v6 Q3 agent).
- **Affected workflow**: agents doing manual diagnostic
  testing of cache resolution.
- **Verdict**: nice-to-have docs note in SETUP.md §8.

### F22 — `[PROGRESS]` dispatch counts are global, not per-sc

`[PROGRESS]` log emits cumulative `<V>V / <U>U / <E>E /
total` tallies.  Axiom-heavy paths use local per-sc
counters that fold back to global only at end-of-sc.
During multi-minute sc enumeration the printed counts
appear frozen, looking like a wedge.

**Verification (2026-06-09):** confirmed in
`synth/solver.py:1109-1115` — explicit comment "Fold
local counters into the outer totals" with code:
```python
lean_dispatch_hits += lean_hits_local[0]
lean_dispatch_misses += lean_misses_local[0]
lean_dispatch_errors += lean_errs_local[0]
```
Globals frozen during axiom-heavy enumeration.

- **Cost when hit**: false-wedge concern; agent may
  premature-stop.
- **Affected workflow**: any sufficiently-long axiom-heavy
  benchmark.
- **Verdict**: nice-to-have observability improvement.

### F23 — F17 partial-τ infix only tracks current loop's τ

Chain-aware sc8 dumps have `loop_id=L0` (via atom_ref
fallback) so the `_partialNofM_` infix tracks τ@L0 only.
sc8's chain hyps also include τ@L1 (from L1's abstract
transition), and the τ@L1 subset varies independently.

**Verification (2026-06-09):** confirmed in
`synth/lean_backend/verify.py:151` —
`_tau_key = f"tau@{loop_id}"` only considers the current
loop's τ.  Multi-τ obligations aren't reflected in the
infix.

- **Cost when hit**: wasted audit time investigating
  partial-τ@L1 dumps thinking they're full-τ.
- **Affected workflow**: chain-aware HARD benchmarks.
- **Verdict**: extension to `_L0_3of3_L1_2of3_` infix
  format would be precise.

### F25 — `_consult_companions` typechecks every cache hit

Per-cache-hit `lake env lean` typecheck costs ~2–3s for
soundness (guards against stale companion content).  With
many subsets, this accumulates linearly.

**Verification (2026-06-09):** confirmed in
`synth/lean_backend/verify.py:716-719` — every hit
triggers `_typecheck(path, timeout_s)` which spawns
`lake env lean`.

- **Cost when hit**: pure wall-clock; not a correctness
  issue.
- **Affected workflow**: any benchmark with many cache
  hits per constraint.
- **Verdict**: nice-to-have perf — could short-circuit via
  filename + signature trust (lossier but faster) for
  repeated runs of the same benchmark.

### F26 — No per-VALID τ subset logging

`[PROGRESS]` emits V/U/E counts but doesn't say which τ
subsets are passing.  Authors can't see which subsets
work until partial dumps appear.

**Verification (2026-06-09):** confirmed —
`valid_assignments.append(...)` has no associated `print`
calls anywhere in `solver.py`.  Only aggregate counts in
`_maybe_print_progress`.

- **Cost when hit**: opacity during multi-minute runs;
  paired with F22 amplifies false-wedge risk.
- **Verdict**: nice-to-have observability.

### F27 — Document pre-authoring `.solved.lean` candidates

v6 Q1 agent's workflow: write a Python hash-computer
script to compute signature hashes for several τ subsets
upfront, then lift proofs from a reference benchmark
verbatim with mechanical substitution.

**Verification:** v6 Q1 used this strategy successfully
to land 873.5s verified solution; the workflow itself is
the evidence.

- **Cost when not documented**: future MEDIUM authors
  rediscover the strategy independently.
- **Verdict**: doc addition to REC 11.6.

---

## Banked from v7 audit

Source: v7 Q2 (`suffix_sum`), v7 Q3 (`matrix_diagonal_sum`).

### F29 — Right-to-left UF axiom needs explicit `(i-1)+1 = i` rewrite

The right-to-left recurrence `∀k. k < m → sum_suffix(A, k,
m) = A[k] + sum_suffix(A, k+1, m)` instantiates at
`(i-1)+1 = i`, but Lean doesn't auto-simplify arithmetic
inside UF args.  Author needs explicit
`have h_idx : (i-1)+1 = i := by omega` before
`rw [user_axiom_1]`.

**Verification:** v7 Q2 agent observed this in their
proof attempt and worked around it.  Lean's `simp` doesn't
rewrite inside UF application argument positions —
plausible language behavior.

- **Cost when hit**: ~5 min the first time.
- **Verdict**: doc note in problem.skill near REC 11's
  axiom-recurrence guidance.  Only one occurrence so far
  (`suffix_sum`); wait for second.

### F31 — 2D `rw [← h_i]` over-rewrites when UF takes index arg twice

v7 Q3 `matrix_diagonal_sum`'s first sc4 proof copy-pasted
`sum_array`'s template `rw [← h_i]; exact h_tau_2`.  With
`h_i : i' = n` and goal `diag_sum A n n`, the backward
rewrite swapped BOTH occurrences of `n`.  Fix:
`rw [h_i] at h_tau_2; exact h_tau_2`.

**Verification:** v7 Q3 agent observed this directly in
their proof attempt.  Lean's `rw` rewrites all matching
occurrences by default — standard language behavior.

- **Cost when hit**: ~10 min.
- **Verdict**: doc note in problem.skill chain-aware
  section.  One 2D benchmark; wait for second.

### F32 — REC 11.5 silent on existential-dual flag-fold

REC 11.5 documents the universal-gate guidance for
flag-folds.  The existential-dual case uses a
mathematically-equivalent gate that's effectively a no-op,
but the agent has to reverse-engineer this from
`is_sorted`.

**Verification (2026-06-09):** confirmed by reading
REC 11.5 — text covers "asserts a property about an
array read at a 'next' index" but doesn't address the
existential-dual flag-fold pattern.

- **Cost when hit**: ~3–5 min reverse-engineering.
- **Verdict**: 3–5 line addition to REC 11.5.

---

## Banked from v8 audit

Source: v8 Q1 (`is_palindrome`), v8 Q2 (`fibonacci_array`),
v8 Q3 (`find_max_index`).

### F33 — Two-pointer ranking `j - i + 1` and coupling atom

For two-pointer-toward-middle benchmarks: ranking must be
`j - i + 1` (not `n - i`) — the `+1` keeps it ≥ 0 at n=0
entry where `j = -1`.  Load-bearing atom `i + j == n - 1`
couples the pointers so the τ flag-fold uses a prefix-only
quantifier yet entails the full symmetric post.  Atom
`i <= j + 1` is the ranking-lb invariant.

**Verification:** v8 Q1 used this design and synthesized
in 0.95s — the working design is the evidence.

- **Cost when hit**: 5–10 min reverse-engineering from
  `reverse_array`.
- **Verdict**: one-paragraph REC pointer.  Only if a
  second two-pointer benchmark surfaces.

### F34 — Canonical LAST-occurrence encoding

For "find LAST occurrence of X" patterns: the canonical
τ encoding is **(weak-≤ over whole prefix) ∧ (strict-<
over strictly-after-witness range)**.  Branch-update on
`>=` (not `>`) keeps the strict-< invariant inductive
because the empty strict-after range is vacuously true
after each witness-jump.

**Verification:** v8 Q3 used this design and synthesized
in 0.93s — the working design is the evidence.

- **Cost when hit**: ~10 min.
- **Verdict**: prescriptive nugget worth adding to REC 5
  if/when a second LAST-occurrence benchmark surfaces.

### F35 — SSA-list init transitions rejected in chain-aware bundle translator

`NotImplementedError: chain-item SB: non-dict atom` raised
when an SSA-list transition appears on a chain-prefix SB.
Workaround: collapse into one parallel
`Update(Update(...))`.

**Verification (2026-06-09):** confirmed in
`synth/lean_backend/translate.py:1841-1844`:
```python
if not isinstance(atom, dict):
    raise NotImplementedError(
        f"chain-item SB({item.block_id}): non-dict atom"
    )
```

- **Cost when hit**: ~5 min once the error message points
  at the line.
- **Affected workflow**: chain-aware benchmarks with
  multi-element SB init (e.g. `fibonacci_array`'s
  two-base case).
- **Verdict**: either (a) lift SSA-list support into the
  chain translator, or (b) clearer error message.  Real
  framework gap, one occurrence so far.

### F37 — `store_off` lemma absent from `SynthLean.Core`

When `h_eq : ¬(k = i)`, `simp [store, h_eq]` sometimes
fails to close `store C i v k = C k`.  Workaround:
`have h_store_off : store C i v k = C k := by simp [store,
h_eq]; rw [h_store_off]`.

**Verification (2026-06-09):** confirmed Core.lean has
`store` and `store2d` definitions but no `store_off` or
equivalent off-index transparency lemma.

- **Cost when hit**: ~5 min once the workaround is known.
- **Verdict**: add a `store_off` lemma to Core so authors
  don't fight `simp`.  Real Core gap.

### F38 — How to check which translator variant fires

When authoring `.solved.lean` companions, agents currently
have no easy way to verify which translator variant
(`theorem_for_entry_bundle` vs
`theorem_for_entry_bundle_chain`,
`theorem_for_chain_bundle` vs
`theorem_for_chain_bundle_chain`) will be dispatched.

**Verification (2026-06-09):** verified twice.  First by
discovering v8 Q2's misreading produced 2 dead
`.solved.lean` files.  Second by writing and running the
recipe:

```python
from synth.expand import expand, SB
from synth.lean_backend.translate import _linearize_path
expand(PROBLEM)
chain, target_idx, enc_lid = _linearize_path(PROBLEM.template, "L0")
chain_has_loops = any(not isinstance(it, SB) for it in chain[:target_idx])
use_chain = chain_has_loops or enc_lid is not None
print(f"_use_chain = {use_chain}")  # False → non-chain; True → chain
```

- **Cost when missing**: ~10 min wasted authoring per
  redundant variant.
- **Verdict**: 5-line recipe in problem.skill REC 11.6
  (near chain-aware section).  **This is the only v8 Q2
  finding that survived investigation.**

---

## How this backlog is used

1. **Periodically re-examine** when a new round surfaces a
   finding adjacent to an existing entry — second
   occurrence usually promotes "nice-to-have" to "worth
   shipping."
2. **Aggressively delete** entries that don't survive
   verification.  v6→v8 audits deleted 6 of 20 originally-
   banked items as false positives, already-covered, or
   over-extrapolation.
3. **Reference for outside contributors** — if any of
   these bite you, this file is the ground truth on
   "yes, we know, we're tracking it."

For the round-by-round narrative + the
shipped-vs-banked-vs-rejected accounting, see
[`COMMUNITY_VALIDATION_REPORT.md`](./COMMUNITY_VALIDATION_REPORT.md).
