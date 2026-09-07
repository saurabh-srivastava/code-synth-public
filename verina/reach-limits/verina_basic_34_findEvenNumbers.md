# verina_basic_34 (findEvenNumbers) — NOT-EXPRESSIBLE note

**Verdict: NOT-EXPRESSIBLE** in this repo's fixed-template IR as a
verifiable synthesis task.  The filter is *syntactically encodable*
(the IR accepts a `Problem` for it) but *not tractably verifiable*:
every soundness-critical proof obligation wedges.  An empirical probe
(faithful index-encoded attempt) returned `needs-helpers` after
185.8s with **0 / 63 valid Lean dispatches** (11 unknown, 52 hard
elaboration errors) — the entry bundle, coverage, both branch
inductives, and the final ⇒ post all abandoned.

No benchmark file is shipped (a non-verifying benchmark would pollute
the corpus / regression).  This note is the deliverable.

---

## VERINA spec (source of truth)

    findEvenNumbers(arr : Array Int) -> Array Int
    precond  : True
    code     : arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]

Postcondition (three conjuncts, all over `arr.toList` / `result.toList`):

1. `result.all (fun x => isEven x ∧ x ∈ arr.toList ∧
                          result.toList.count x = arr.toList.count x)`
   — every result element is even, is in `arr`, and has the **same
     multiplicity** in `result` as in `arr`.
2. `arr.all (fun x => isEven x → x ∈ result.toList)`
   — every even element of `arr` is in `result`.
3. order preservation: for evens `x, y`, if `x` precedes `y` in `arr`
   (`idxOf x ≤ idxOf y`) then `x` precedes `y` in `result`.

This is a **filter**: keep the even elements, in order.

---

## Why the fixed-template IR cannot verify this

### What the IR *can* do (so these are NOT the blocker)

- **Data-dependent output length is fine.**  Arrays are total Z3 maps
  (`ArraySort(Int,Int)`) with a *separate* `int` length variable —
  there is no intrinsic `.size`.  A "length = number of evens" value
  is just an `int` output equal to a count UF, exactly as
  `count_zeros` / `verina_basic_57_count_less_than` already prove
  `c == count(A, n)`.  So the task's stated crux ("no way to express
  output length = count of a predicate") is, strictly, *sidesteppable*
  — the length is expressible as an int output.
- **The conditional write is fine.**  `acc.push x` on the even branch
  becomes a `Store` at a running counter `j`:
  `res := Update(res, j, A[i]); j := j + 1` inside an even branch of a
  `Loop(SB(n=2))`, incrementing `j` only when kept.  This is just
  `count_zeros`'s conditional counter fused with `array_concat`'s
  store.

### The real blocker: the postcondition's list/multiset/order semantics

The three conjuncts are stated over `toList`, `count` (multiset
multiplicity), `∈`, and `idxOf` (position-in-list) of a
**variable-length output sequence**.  **The IR has no primitive for
any of these** — an array is a total map over *all* integer indices,
with no notion of "the list of its first `len` elements", no multiset
`count`, no membership, no `idxOf`.  To even *state* the post you must
re-encode it as a **two-way position bijection** between
even-input-positions and output-positions, via a count-of-evens UF
`ce(A,i)` (= number of evens in `A[0..i)`).  The load-bearing
invariant then becomes

    ∀p. 0≤p<i ∧ isEven(A[p]) ⇒ res[ce(A, p)] == A[p]

i.e. **a UF (`ce`) applied INSIDE an array `Select` index, INSIDE a
universal quantifier**.  Two things make this beyond the framework's
demonstrated tractable surface:

- **Clobber-freedom under a quantified Store.**  Preserving the
  invariant across the even branch's `Store(res, j, A[i])` (with
  `j = ce(A,i)`) requires proving the store does not overwrite an
  earlier even's slot `ce(A,p)` for `p<i` — i.e. `ce`
  monotonicity/injectivity *under quantifiers, against an array
  Store*.  This is precisely the E-matching cliff the tractability
  table flags (quantified + array-Store τ → hours/hangs).  In the
  probe this obligation (sc2, even-branch inductive) returned only
  ERROR/UNKNOWN, never valid.
- **Even this is only PARTIALLY faithful.**  The `res[ce(A,p)]==A[p]`
  relation captures conjunct 2 (each even present at its rank) and
  conjunct 3 (order — ranks are monotone in position), and
  multiplicity via the bijection.  But it does **not** capture
  conjunct 1's *forward* direction — "every `result[k]` for `k<len` is
  even" = surjectivity of the rank map onto `[0,len)`.  Stating that
  needs a **second inverse UF** `pos(A,k)` (= input position of the
  `k`-th even) with `res[k] == A[pos(A,k)]` — doubling the
  UF-indexed-Store-under-∀ machinery that already wedged.

### Empirical evidence (probe, faithful-partial encoding)

Template `SB() >> Loop(SB(n=2)) >> SB()`; outputs `res : int[]`,
`outlen : int`; UF `ce(A,i)` with the count recurrence + a
monotonicity axiom; post `outlen == ce(A,n) ∧ ∀p. …res[ce(A,p)]==A[p]`.

    wall: 185.8s → FAILED: needs-helpers
    Lean fallthrough: 0 valid, 11 unknown, 52 error (out of 63 calls)
    Wedged & abandoned:
      sc0  safety-bundle-entry   (loop entry:  0 == ce(A,0), the sc0 UF-cliff)
      sc1  coverage              (A[i]%2==0 ∨ A[i]%2!=0)
      sc2  safety  branch 0      (even-branch inductive: UF-indexed Store preservation)  ← core cliff
      sc4  safety  branch 1      (odd-branch inductive)
      sc7  safety-bundle-post    (final ⇒ post: the compaction bijection)

Every soundness-critical obligation abandoned; **52 of 63** Lean calls
were hard elaboration *errors* (not mere cold-cache timeouts),
confirming the UF-indexed-Store-under-∀ + `%`-evenness shapes are
outside the generic tactic chain's reach, not one-helper-away.

---

## Sidestep encodings for future IR work

The write mechanism is already fine; the gap is entirely in the
**post-language** and the **filter-preservation proof pattern**:

1. **Compacted array + returned length is the right output shape** —
   and is already representable (`res : int[]` + `outlen : int`).  The
   missing piece is not the shape but the *specification vocabulary*
   for reasoning about `res[0..outlen)` as a sequence.
2. **Add a small "sequence view" post-vocabulary** — derived
   predicates for multiset-count, membership, and idxOf over
   `A[0..len)` (as macros expanding to `ce`-style counting UFs), so a
   filter post can be *stated* without hand-rolling the bijection each
   time.
3. **A reusable "filter-preserves-compaction" proof lemma** (Tier-1,
   analogous to Slice 2.C's `flip_preserves_im`): prove once that a
   `Store` at `j = ce(A,i)` on the even branch preserves
   `∀p<i. even ⇒ res[ce(A,p)]==A[p]`, given `ce` monotonicity.  This
   is the load-bearing sc2 obligation; a hand-authored helper for it
   is what the probe's wedge detector is asking for.  With that helper
   (plus the sc0 one-line UF-cliff helper and an sc7 final-bundle
   helper), the *partial* post (conjuncts 2+3+multiplicity) might
   close; full fidelity (conjunct 1 forward) additionally needs the
   inverse-position UF above.
4. **Boolean-mask alternative** (keeps output length = `n`): emit a
   parallel `keep : int[]` mask instead of compacting.  This dodges
   the data-dependent length and the UF-indexed Store entirely, but is
   **not a faithful port** — VERINA's `result` is the *compacted*
   array, and its `count`/`idxOf`/`toList` conjuncts are about the
   compacted sequence, not a masked full-length one.

**Bottom line:** the blocker is not the data-dependent length (that is
expressible) — it is the multiset + order + membership postcondition
over a *variable-length output sequence*, which has no IR primitives
and forces a UF-indexed-`Store`-under-quantifier encoding that lies
beyond the framework's demonstrated tractable/generic-tactic surface.
