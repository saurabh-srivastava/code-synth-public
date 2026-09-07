# Benchmarks — status, discoveries, and caveats

Comprehensive index of every committed benchmark, organized by
tier.  This file supersedes the deleted `STRETCH_STATUS.md` and
the experimental "Dashboard" section that briefly lived at the
bottom of `README.md`.

## Reading guide

Each entry includes:

- **Path** — relative to repo root, e.g. `benchmarks/intsqrt.py`.
- **Verifies via** — which backend(s) close the obligations:
  - **Z3** = SMT alone is enough (sound mode trusted).
  - **Z3 + Lean** = some classes route through Lean dispatch
    (curated `.solved.lean` companions, generic tactic chain, or
    Tier-3 helper citations).
- **Result** — `V` (verification — algorithm hand-encoded as
  template + atoms; framework verifies the obligations close) or
  `S` (synthesis — framework picks an atom subset from a
  hand-supplied pool such that the obligations close).  Most
  "synthesis" in this corpus is the latter; the framework
  doesn't invent the algorithm shape.  See "Stronger discovery
  moments" at the bottom for the few cases where the atom
  picking did real work.
- **Time** — last-known wall-clock seconds for the synth pass.
  Captured from `tests/regression_timings.json` where available;
  otherwise a manual measurement.
- **Helpers tier** — for benchmarks with Lean companion files:
  - 🛡️ **Tier-1** — `Helpers.lean` theorems with full proofs.
    Trust comes from Lean's kernel.
  - 📦 **Tier-2** — Helpers with `axiom` declarations.  Trust
    scope: "the user vouches this is the algorithm's claim."
    Documented inline in the file with a proof sketch.
  - 📋 **`.solved.lean` companions** — per-class proofs in the
    dump dir alongside `.failed.lean` records of subsets the
    framework correctly rejected.
- **Discoveries** — concrete things the framework / a debugging
  session surfaced.
- **Caveats** — honest framing.  What does NOT count as algorithm
  discovery; where the framework wedges; whether the proof rests
  on axiomatized black boxes.

---

## Tier: Foundational loop benchmarks (Phase 1-3)

The "starter set" — small, hand-curated atom pools where the
expected solution is clear.  These benchmarks underpin every
later capability claim.

### Numerical loops with scalar invariants

**Integer square root via repeated subtraction** —
`benchmarks/intsqrt.py`

  - Verifies via: Z3 only.  Time: ~1.1s.  Result: S, 2 solutions.
  - Spec: post-loop `v == i² ∧ x < i² (= (i+1)·(i+1))`, ϕ = `x − (i−1)²`.
  - Discoveries: this is the POPL'10 Eq.(7) shape.  Z3 finds
    the nonlinear ranking function from a candidate list once
    cumulative-else is dropped (Phase 2.5 lesson #5).
  - Caveat: the candidate ϕ list is hand-curated to include
    `x − (i−1)²`; framework picks among 3 candidates.

**Triangular sum 1+2+…+i** — `benchmarks/sumi.py`

  - Z3.  1.1s.  S, 2 solutions.
  - Quadratic invariant `2s = i(i+1)`; lower-scored solution drops
    the redundant `0 ≤ i` atom (direct evidence Phase 2's
    conjunctive τ search is doing real work).

**Multiplication by repeated addition** — `benchmarks/mul.py`

  - Z3.  2.2s.  S, 2 solutions.  Bilinear invariant `p = a·i`
    with three τ atoms (`p = a·i`, `0 ≤ i`, `i ≤ b`) plus three
    distractors.  Framework correctly subsets the load-bearing
    atoms.

**Integer division (quotient + remainder)** — `benchmarks/intdiv.py`

  - Z3.  2.2s.  S, 2 solutions.  Repeated-subtraction division
    computing `q, r` with `x = q·y + r ∧ 0 ≤ r < y`.  Same
    bilinear-invariant shape as `mul`.  Breadth coverage; no new
    framework features.

**Bresenham line drawing — termination + algebraic invariant** —
`benchmarks/bresenham.py`

  - Z3.  0.9s.  S, 2 solutions.  Bilinear algebraic invariant
    `v = 2dy·x − 2dx·y − dx + 2dy`.  Strengthened post forces
    the algebraic atom into the chosen τ subset (otherwise the
    framework picks the trivial `0 ≤ x ≤ dx` and skips the
    interesting one — Phase 3.O lesson #22).

**Bresenham line drawing — full quantified pixel-correctness** —
`benchmarks/bresenham_full.py`

  - Z3.  5.0s.  S, 2 solutions.  Post: `∀k. 0 ≤ k < dx ⇒ −dx ≤
    2·dy·k − 2·A[k]·dx ≤ dx`.  Classical POPL'10-era hard
    benchmark.  Z3 instantiates the quantifier against array
    Stores while discharging bilinear arithmetic — running in
    seconds is a real validation of Phase 3.L monotonicity-aware
    enumeration + Phase 3.X.3 push/pop reuse composing well.

### Branched + array-write loops

**Acyclic absolute value** — `benchmarks/abs.py`

  - Z3.  <0.1s.  S, 3 solutions.  Three guard partitions for
    `y = |x|`: `x<0/else`, `x>0/else`, `x<=0/else`.  Phase 2.5's
    cumulative-else machinery for `SB(n=2)` validated here.

**Saturating subtraction** — `benchmarks/sat_sub.py`

  - Z3.  <0.1s.  S, 3 solutions.  Same shape as `abs` for
    `r = max(0, a−b)`.

**Array maximum via while-loop** — `benchmarks/max_array.py`

  - Z3.  9.0s.  S, 5 solutions.  Single loop + SB(n=2) +
    quantified invariant `∀k. A[k] ≤ m`.  Five solutions because
    the post is **underspecified** — `m = INT_MAX` or any upper
    bound satisfies it (Phase 3 lesson #7).  Caveat: weak post
    admits weak solutions; this is informative for LLM-supplied
    specs.

**Array zero-fill** — `benchmarks/array_zero.py`

  - Z3 + Lean.  39.9s.  S, 2 solutions.  Loop with array Update
    `A := Update(A, i, 0)` + quantified prefix-zero invariant.
    Slow because quantified-array dispatch is axiom-heavy.

**Sum of array (recurrence + UF)** — `benchmarks/sum_array.py`

  - Z3 + Lean (📋 2 `.solved.lean` companions).  100.6s.  S, 1
    solution.  Loop computes `s = sum(A, n)` with `sum`
    declared as an UF + recurrence axiom.  First axiom-heavy
    benchmark; Lean closes 2 of ~7 UNKNOWN classes that Z3 can't.
    Caveat: per-class cost is 100ms–10s due to E-matching on
    universal axioms.

**Fibonacci (axiom-heavy slow suite)** — `benchmarks/fib.py`

  - Z3 + Lean.  ~5 minutes (slow suite only).  S, 3 solutions.
    Iterative Fibonacci with `fib` as an UF + recurrence axiom.
    Per-class Z3 check is expensive (axiom E-matching); kept out
    of quick suite to avoid burning regression time.

### Recursion (Phase 3.E – 3.J)

**Recursion to a constant** — `benchmarks/rec_const.py`

  - Z3.  <0.1s.  S, 2 solutions.  First `_recur` atom + a
    per-procedure ranking `phi@PROC`.  Recursive call decreases
    `n`, so `phi@PROC = n` works.  Published + variant solutions
    found.

**Recursion to negation** — `benchmarks/rec_neg.py`

  - Z3.  <0.1s.  S, 2 solutions.  Non-identity `ret` transform
    (`result := -_r_result`).  Validates the recur-ret binding's
    post-processing layer.

**Recursive array zero-out** — `benchmarks/rec_zero_array.py`

  - Z3.  <0.1s.  S, 1 solution.  Array threaded through the
    recursive call; vacuous-base-case trick at `n = 0`.  First
    benchmark proving Phase 3.F's array+recursion + `ret`
    enrichment works.

**Recursion + acyclic-step chain** — `benchmarks/rec_zero_array_chain.py`

  - Z3.  <0.1s.  S, 1 solution.  `Recur >> SB(n=1)` shape — the
    POPL'10 `~;◦` template.  Validates Phase 3.G's intermediate
    state bindings.

**MergeSort-shaped recursion** — `benchmarks/rec_zero_double.py`

  - Z3.  <0.1s.  S, 1 solution.  `~;~;◦` shape (two recursive
    calls + acyclic-step).  Structural exercise; the second
    recursive call is redundant for the spec.  Phase 3.H.

**Branched recursion in a chain** — `benchmarks/rec_zero_array_branched.py`

  - Z3.  0.1s.  S, 1 solution.  `Recur >> SB(n=2)` — independent
    guards per branch (Phase 3.I dropped cumulative-else).

**Recursion with clamped ranking** — `benchmarks/rec_clamped_phi.py`

  - Z3.  <0.1s.  S, 1 solution.  Demonstrates Phase 3.J's
    vacuous-Fpre ranking refinement — the chosen ϕ is monotone
    only where Fpre holds.

**Cover benchmarks** —
`benchmarks/cover_loop_branched_recur.py` and
`benchmarks/cover_chain_branched_recur.py`

  - Both Z3 only, <0.1s.  Coverage tests for the Lesson #27 bug
    class (SB-branch recur decrease).  Pin a degenerate solution
    that the synthesizer must reject; regression guard.

### Nested loops

**Doubly-nested counter** — `benchmarks/nested_loop.py`

  - Z3.  4.8s.  S, 3 solutions.  First nested-Loop benchmark
    (Phase 3.K).  Inner loop is a no-op; the structural exercise
    is the abstract inner-Loop transition + frame equations.
    Without frame eqs, outer ranking decrease fails.

**Triangular zero-fill (nested + array writes)** —
`benchmarks/nested_zero_array.py`

  - Z3.  0.2s.  S, 1 solution.  Outer body writes `A[i] := 0`
    before the inner Loop; frame preserves A across abstract
    inner transition.  Phase 3.M.  Solver picks a MORE minimal
    τ_inner than the human witness (dropped `0 ≤ j`, `i < n` —
    both derivable from antecedent path).

**Bubble sort — first real sort** — `benchmarks/bubble_sort.py`

  - Z3.  2.3s.  S, 1 solution.  Nested loops + quantified
    inductive + conditional swap.  Phase 3.P.
  - **Discovery moment**: the synthesized τ includes a *bilateral*
    quantified atom `∀p, q. 0 ≤ p ≤ q < n ∧ q ≥ n-i ⇒ A[p] ≤ A[q]`
    that subsumes both suffix-sortedness and prefix-dominance.
    Z3 doesn't enumerate two atoms when one bilateral atom
    suffices.  This is the kind of structural insight the user
    might not write by hand (lesson #23).

**Selection sort** — handled via `Helpers.lean`; see Stretch
tier below.

**Matrix init (2D array)** — `benchmarks/matrix_init.py`

  - Z3.  6.3s.  S, 1 solution.  First `int[][]` 2D-array
    benchmark (Phase 3.S).  1D-flattening alternative (`A[i*n + j]`)
    wedged Z3 on quantified nonlinear arithmetic; native 2D
    sidesteps the wedge.

**Matrix diagonal sum (2D + UF + axiom)** —
`benchmarks/matrix_diagonal_sum.py`

  - Lean dispatch.  128s.  S, 1 solution.  First
    **agent-authored** 2D benchmark (v7 community-validation,
    HARD tier).  UF `diag_sum(A, n, k)` with base +
    recurrence axioms.  Validates that the Phase 3.S
    `int[][]` extension is agent-accessible: atom strings
    like `A[i][i]` parse cleanly through Z3 (nested Select)
    and Lean (`(A k) k`), UF arg-type `int[][]`
    auto-parenthesizes to `(Int → Int → Int)`.  Identical
    structure to `sum_array` but with 2D indexing.

**Is palindrome (two-pointer toward middle)** —
`benchmarks/is_palindrome.py`

  - Z3.  0.95s.  S, 1 solution.  First
    **agent-authored** two-pointer-toward-middle benchmark
    (v8 community-validation, HARD tier).  Template
    `SB() >> Loop(SB(n=2)) >> SB()` with two indices
    `i, j` moving in opposite directions and termination
    `i >= j`.  Key design: ranking `phi = j - i + 1` (not
    `n - i`) — the `+1` keeps it ≥ 0 at n=0 entry where
    `j = -1`.  Atom `i + j == n - 1` couples the pointers
    so τ uses a prefix-only quantifier yet entails the
    full symmetric post.

**Fibonacci array (self-referential array recurrence)** —
`benchmarks/fibonacci_array.py`

  - Lean dispatch.  137s.  S, 1 solution.  First
    **agent-authored** self-referential array benchmark
    (v8 community-validation, HARD tier).  Each `C[k]`
    depends on `C[k-1]` and `C[k-2]` (read two prior
    elements of the SAME array being written).  Init SB
    writes both base elements
    `Update(Update(C, 0, 0), 1, 1)` in one parallel
    assignment; loop body reads + writes incrementally.
    UF `fib` with 3 axioms (two-element base + recurrence).
    The first `.solved.lean` from
    `theorem_for_entry_bundle` (the non-chain dispatch);
    chain-aware companions would only be needed for
    multi-loop templates.  (See
    `COMMUNITY_VALIDATION_BACKLOG.md` F38 for the recipe
    to check which translator variant fires.)

---

## Tier: Phase X "batch" corpus

Fifty simple benchmarks committed in 9 batches.  Each carries
an English description in its top-of-file docstring (the user-
phrased spec the LLM front-end would receive).  All Z3-decidable,
no Lean dispatch; most run in <1s.  Verified/Synthesized = S
(framework picks atoms from hand-supplied pool of 3-6 candidates
per hole; expected_solutions = 1 or 2).

Why this corpus matters: the `(description, Problem)` pairs are
the training data for the Phase Y.2 driver-LLM, which would
read English specs and emit `Problem` objects.

### Batches

  - **Batch 1** (`min_array`, `array_fill`, `array_copy`,
    `increment_array`, `negate_array`).  All <1s, classic
    array primitives.
  - **Batch 2** (`max2`, `add_arrays`, `clamp_array_positive`,
    `array_double`, `subtract_arrays`, `min_index`,
    `array_swap`, `linear_combination`, `pairwise_max`).
    Mostly <1s; introduces SB(n=2) branched bodies.
  - **Batch 3 (axiom-heavy)** — `factorial`, `count_zeros`,
    `array_product`.  Each uses a UF + recurrence axiom; needs
    Lean dispatch.  `.solved.lean` companions in the Y2Corpus
    dirs; total ~few seconds each in quick suite.
  - **Batch 4** (`max3`, `abs_diff`, `last_element`, `mid3`,
    `swap_first_last`, `scalar_clamp`, `range_init`).  All <1s.
  - **Batch 5** (`abs_array`, `saturate_add`, `max_min_diff`,
    `array_max_index`).  Mostly <1s.
  - **Batch 6** (`array_increment_at`, `all_positive`,
    `array_set_const`, `scalar_max4`, `count_equal`).  All
    <1s.
  - **Batch 7** (`array_concat`, `find_first_pos`,
    `min_max_pair`, `array_rotate_left`, `array_shift_right`,
    `dot_product`, `sum_first_k`, `array_neg_count`).
    Notable slow: `array_rotate_left` 354s, `array_shift_right`
    111s — quantified-array reasoning over array Update chains
    bites here.
  - **Batch 8** (`array_max_val`, `array_min_val`, `abs2`,
    `sign`, `range_init_offset`, `gcd`, `power_of_two`).  Mostly
    <1s.
  - **Batch 9** (`reverse_array`, `is_sorted`, `scalar_min4`,
    `clamp_array_range`, `array_index_of`).  Notable slow:
    `reverse_array` 539s.  The reverse_array curation banked a
    lesson (the ranking-LB constraint must hold at EVERY
    τ-consistent state including loop-entry where guard is
    false — at `n=0` the natural `ϕ = hi - lo` is negative; fix:
    `ϕ = hi - lo + 1`).

---

## Tier: Stretch corpus (Phase X.S — edge of tractability)

Eleven benchmarks that pushed the framework's reach.  All
verified end-to-end; some required new translator features.

### Sorting algorithms

**Selection sort** — `benchmarks/stretch/` and Phase 3.Q in CLAUDE.md

  - Z3 only, 312s standalone.  S, 1 solution.  The slow time
    (vs bubble sort's 2.3s) reflects where the swap lives — in
    selection sort the swap is OUTSIDE the inner loop, so the
    expensive Store-of-Store array reasoning happens inside the
    outer body's final-bundle constraint, which also enumerates
    outer τ.  Lesson #24 banked.

**Insertion sort** — `benchmarks/insertion_sort.py`

  - Z3 + Lean (🛡️ Tier-1, 1 theorem proven). 6.5s.  S, 1
    solution.  Inner loop walks the inserting element leftward
    by swapping with the "wall" `A[j-1]`.  Three τ_inner atoms:
    left-portion sorted, right-portion sorted, wall lower-bound
    (`A[j-1] ≤ A[k]` for `k ∈ (j, i]` when `j > 0`).  Wall-LB
    is the dual of bubble sort's bilateral atom — physical fact
    that isn't derivable from sortedness alone (lesson #23).
    The H.4 nested chain-bundle translator unlocked the
    timing improvement (#167 + chain-aware): 412s → 6.5s.

**Merge two sorted arrays** — `benchmarks/stretch/merge_two_sorted.py`

  - Z3 + Lean (🛡️ Tier-1: 6/7 theorems proven; 📦 Tier-2: 1
    axiom).  ~2 min.  S, 1 solution.  Classic 4-phase template
    (init + L0 merge + L1 drain B + L2 drain A).  First chain-
    aware multi-loop benchmark (#167).
  - **Discovery moment**: synthesized the canonical
    `if (A[i] ≤ B[j]) emit A[i] else emit B[j]` merge loop +
    two drain loops from a template + atom pool.
  - **Tier-2 ceiling**: `merge_l2_entry_chain`.  The 6th conjunct
    of τ@L2 entry (`last ≤ A[i]`) is unprovable from the τ
    atoms when `i ≥ n` (no axiom bounds `A[n]`).  In practice
    the L2 guard makes this vacuous, but the entry-bundle
    obligation has to discharge it structurally.  Promoting
    would require strengthening the τ encoding to gate this
    conjunct on `i < n` (which we already did for the per-step
    drains via IR-level τ gating — same trick should apply
    here in a future session).

### Polynomial-multiplication algorithms

**Karatsuba (deg-1 over ℤ)** — `benchmarks/stretch/karatsuba_deg2.py`

  - Z3 only, ~5s.  S, 1 solution.  3-mult deg-1 polynomial
    multiplication.

**Toom-3 (deg-2 over ℤ)** — `benchmarks/stretch/toom3_deg2.py`

  - Z3 only, ~5s.  S, 1 solution.  5-mult deg-2 polynomial
    multiplication; Z3 handles polynomial-identity divisibility
    under `//` automatically.

**Strassen 3×3 — Laderman 23-mult** —
`benchmarks/stretch/strassen_3x3_laderman.py`

  - Z3 only, <60s.  S, 1 solution.  First edge-of-open result:
    Laderman's 23-multiplication algorithm for 3×3 matrix
    multiplication, verified by Z3 polynomial-identity check
    after sympy linear-algebra solve over the 81 a_pq·b_rs
    basis.  Verified across 100 random integer trials before
    synthesis.

**Boolean matmul 3×3 (naive)** —
`benchmarks/stretch/boolean_matmul_3x3.py`

  - Z3 only, ~5s.  V, 1 solution.  27-AND 18-OR naive
    verification.  Caveat: AND/OR semiring has no subtraction,
    so Strassen-style cancellation cannot apply — that's part of
    the point (L1.1 is the open follow-on).

### Discrimination tests (correctly reject planted bugs)

  - **`karatsuba_deg2_discrim_2mult`** — 4 hand-crafted 2-mult
    candidates; framework correctly UNSATs all 4.  Confirms
    3-mult lower-bound recognition for the encoded space.
  - **`toom3_deg2_discrim_wrong_coef`** — `// 3` instead of
    `// 2` in r2 interpolation; correctly UNSAT.
  - **`strassen_3x3_lt23mult_search`** — 23 hand-crafted 22-mult
    candidates each dropping one of Laderman's m_i with
    best-effort output formulas; all 23 correctly UNSAT.
    Confirms framework discrimination at sub-Laderman AND
    surfaces that real discovery needs IR-level parametric m_i
    templates (banked as RESEARCH.md §G.5).

### Algorithmic DP + greedy

**Kadane's max-subarray** —
`benchmarks/stretch/kadane_max_subarray.py`

  - Z3 + Lean (🛡️ Tier-1: 4 theorems proven; 6 axioms; 67
    `.solved.lean` companions).  70s.  S, 1 solution.  The
    canonical "extending vs restarting" two-branch shape.
    H.2.CODEGEN helper-citation unlocked this — pre-codegen,
    Z3-only ran 600s timeout.  Today: 70s thanks to the helper
    short-circuit.

**Modular exponentiation (repeated squaring)** —
`benchmarks/stretch/modular_exponentiation.py`

  - Z3 + Lean (🛡️ Tier-1: 4 theorems + `pow_mod_base` lemma;
    6 axioms; 95 `.solved.lean`).  70s.  S, 1 solution.
    Synthesized the canonical odd/even-branch repeated-squaring
    algorithm.  `modexp_branchN_preserves_inv` proofs use the
    `pow_mod_base` Tier-1 lemma (`Int.le_induction` over k ≥ 0).

**Boyer-Moore majority element** —
`benchmarks/stretch/majority_element.py`

  - Z3 + Lean (📦 Tier-2: 3 algorithmic axioms; 13 axioms total;
    2 theorems; 20 `.solved.lean`).  ~3 min.  S, 1 solution.
    Synthesized the Boyer-Moore voting algorithm.
  - **Tier-2 ceiling**: `boyer_moore_dominance` — the dominance
    invariant `count_eq(A, n, candidate) ≥ count_eq(A, n, v)`
    for every `v` is not derivable from the user's τ atoms; it
    requires structural induction on the algorithm's execution
    trace (or a strengthened τ that captures the "lead since
    adoption" argument).  Promoting it would require an IR-level
    invariant strengthening, not just a Lean proof.

**Floyd-Warshall all-pairs shortest paths** —
`benchmarks/stretch/floyd_warshall.py`

  - Z3 + Lean (🛡️ Tier-1: 14 theorems; 7 axioms).  <60s.  S, 1
    solution.  Triple-nested DP.  Required:
    - The #167 chain-aware translator extension (multi-loop
      chains with nested loops in their bodies).
    - The H.4 cardinality-ordered enumeration (τ@L2 has 11
      atoms; without ordering, 2^11 = 2048 enumeration count
      wedges).
    - The H.2 helper short-circuit (skip per-subset enumeration
      when full τ closes via cited helper).
  - **Tier-2 ceiling**: `sp_self_nonneg` — encodes the
    "non-negative cycles" Pre assumption.  Not a derived fact;
    it's the user's spec, formalized as an axiom for namespace
    consistency.

**Edit distance / LCS-shape DP** —
`benchmarks/stretch/edit_distance.py`

  - Z3 + Lean (🛡️ Tier-1: 6 theorems; 6 axioms).  ~94s.  S, 1
    solution.  Branched inductive (match vs mismatch) over a
    2D `int[][]` table.  All Tier-1 conversions landed today —
    each ~25-50 LOC using `store2d` + axiom rewrites.

**Binary search** — `benchmarks/stretch/binary_search.py`

  - Z3 only, ~30s.  S, 1 solution.  3-phase template after the
    "found-flag" pattern failed.  Surfaced a real capability gap
    (loop ranking-decrease vs found-flag) banked in CS-5.

### Headline

11/11 stretch corpus verified end-to-end.  Of the 28 Tier-3
helpers that landed via H.2.CODEGEN, 23 promoted to Tier-1
theorems (no algorithmic axioms required).  The 3 remaining
Tier-2 axioms are GENUINE CEILINGS that reflect real limits of
the current τ encoding / IR rather than missing proof work:

- `merge_l2_entry_chain` — needs τ encoding strengthening.
- `boyer_moore_dominance` — needs an IR-level invariant move.
- `sp_self_nonneg` — encodes a Pre assumption, not a theorem.

---

## Tier: Cost-bound benchmarks (COST_INVS §1 + §1.5)

Seven benchmarks exercising the resource-bound invariant
infrastructure: `cost_target` on `Problem`, `cost@<lid>` holes,
and the three constraint kinds (`cost-lb`, `cost-decrement`,
`cost-budget`).

**Triangular sum with linear cost target** —
`benchmarks/cost_invs/sumi_cost.py`

  - Z3 only, 0.1s.  S, 2 solutions.  First cost-bound benchmark.
    `cost@L = n − i` against `cost_target = "n"`.  Lean dispatch
    not needed — Z3 closes the linear cost obligations directly.
  - Why interesting: validates that cost-* obligations compose
    with the existing solver pipeline at zero overhead in the
    common (linear) case.

**Negative test (only invalid candidates)** —
`benchmarks/cost_invs/sumi_cost_bad.py`

  - Z3, 0.1s.  V, NoSolution UNSAT.  Same as `sumi_cost` but
    with `cost@L0` candidates that all violate (A) / (B) / (C).
    Regression guard for the cost-decrement constraint emission.

**Multiplication with linear cost target** —
`benchmarks/cost_invs/mul_cost.py`

  - Z3, 0.1s.  S, 2 solutions.  Same linear-cost shape as
    sumi_cost on a different scalar loop.

**Array max with branched body + linear cost** —
`benchmarks/cost_invs/max_array_cost.py`

  - Z3, 0.3s.  S, ≥1 solution.  Cost target = `n` on a loop
    with `SB(n=2)` branched body and a quantified array
    invariant `∀k. A[k] ≤ m`.  Exercises cost-decrement per
    branch.

**Array zero-fill with linear cost** —
`benchmarks/cost_invs/array_zero_cost.py`

  - Z3, 0.2s.  S, 2 solutions.  Quantified prefix-zero atom +
    cost target = `n`.  Array-write cost shape.

**Nested counter with quadratic cost** —
`benchmarks/cost_invs/nested_cost.py`

  - Z3, 1.1s.  S, 3 solutions.  First nested-loop cost
    benchmark.  Synthesized `cost@L0 = (n − i) · (n + 2)`
    (outer remaining cost) and `cost@L1 = n − j` (inner).
    The outer decrement (n + 2) per iteration matches body cost
    = 2 SBs + inner Loop running n times.
  - Why interesting: validates that the §1.5 nested-loop cost
    composition emits the right Z3 obligation and Z3 closes it
    on a polynomial cost expression.

**Bubble sort with quadratic cost — and the NIA tax** —
`benchmarks/cost_invs/bubble_sort_cost.py`

  - Z3, 28.8s.  S, ≥1 solution.  Bubble-sort-shaped nested loop
    with `cost@L0 = (n − i)·(n − i + 1)` quadratic and
    `cost@L1 = n − 1 − i − j` linear.  Total `n·(n + 1)` upper
    bound.
  - **Caveat (encoding lesson #56)**: the same benchmark
    without cost runs in 2.3s.  The 12× tax is Z3-NIA on the
    polynomial cost-decrement.  A heuristic-routing slice
    (detect quadratic cost atoms, route to Lean ahead of Z3)
    would close the gap; deferred until quadratic-cost
    benchmarks become a measured bottleneck.

---

## Tier: Open-problem benchmarks

The "north star #3" work — push at problems whose published
upper or lower bounds are open.  None of these have produced a
genuinely-novel algorithm (the framework's reach is small
bilinear-rank tensors + Lean-axiomatized speculation +
companion sub-tensor verification).  What they HAVE produced:

  - Z3-kernel-checked verification of known results.
  - Comprehensive structural-impossibility narratives at the
    open frontier.
  - Documented framework wedge points.

### L2.1 — Karatsuba over GF(2)[x]

**3-mult deg-1 polymul over GF(2)** —
`benchmarks/open_prbs/karatsuba_gf2/karatsuba_deg2_gf2.py`

  - Z3, <1s.  V, 1 solution.  Reproduces Karatsuba's 3-mult
    algorithm in the GF(2) algebra with `gf2_mul` UF and
    characteristic-2 axioms.

**n=3 (deg-2 polymul over GF(2)) — discrim test** —
`benchmarks/open_prbs/karatsuba_gf2/karatsuba_n3_5mult_search.py`

  - Z3, <1s.  V (UNSAT).  Direct SAT search for a 5-mult
    algorithm in the encoded space; UNSAT.  This is a
    framework-checked lower bound for the specific bilinear
    shape we encoded (not a proof of the general open problem,
    but it rules out the simplest natural shape).

**n=5 K=13 direct SAT search** — `scratch/.../karatsuba_gf2_n5_k13/`

  - TIMEOUT after 4 hours.  Framework wedges past ~300 search
    variables on direct rank-1 SAT.  Documented as the
    framework's reach limit for this style of search.

### L1.2 — Hopcroft-Kerr R(2,3,2)

`benchmarks/open_prbs/hopcroft_kerr_2x3x2/`

**Verify Hopcroft-Kerr's K=11 algorithm** — `verify_k11.py`

  - Z3 + (Lean axiom for sub-algorithm correctness), seconds.
    V.  Reproduces the published 11-mult algorithm via block
    decomposition: Strassen 2×2 + outer-product 2×1.

**Sub-tensor exact bounds** — `companion_bounds.py`

  - Z3, <1s each.  V (tight).  R(2,3,1) = R(2,1,3) = 6 nailed
    down via direct SAT search.

**K=10 speculation sweep (6 structural classes)** —
`sweep_speculations.py`

  - Z3, <75s per class.  V (all UNSAT).  Six structural classes
    enumerated, each pinning a verified sub-algorithm (Strassen,
    outer product, naive 2×2) as a Lean axiom and searching the
    `K_extra` parametric rank-1 supplements.  All six UNSAT —
    comprehensive structural-impossibility narrative for the
    enumerated shapes.

**Direct K=10 SAT search** — TIMEOUT 2 hours.  Documented as a
framework wedge.

### L1.5 — Karstadt-Schwartz fewer-adds Strassen 2×2

`benchmarks/open_prbs/karstadt_schwartz_2x2/`

**Strassen K=7 baseline** — `verify_baselines.py`

  - Z3, 0.03s.  V.  Σ\|nz\| = 36, 18 additions.  Sanity baseline.

**Literal-form lower bound** — `search_min_adds.py`

  - Z3, 288s.  V (UNSAT at Σ\|nz| ≤ 34).  Framework-checked
    lower bound `Σ\|nz| ≥ 35` for ±1 K=7 bilinear decompositions.
    Distinct from Heun/Probert's SLP-count bound — this is the
    literal coefficient nonzero count, which the framework
    pinpoints to within 1 of the conjectured value (35 or 36;
    threshold 35 itself wedges Z3).

**SLP per-side decomposition** — `slp_forms.py`

  - Z3, per-side 0.13–186s.  V.  Strassen α/β/γ per-side
    minimum SLP costs computed: 5 + 5 + 8 = 18 total.  Matches
    the standard count exactly.

**Joint encoder (bilinear + SLP)** — `encoding_joint.py`

  - TIMEOUT at 500s on sanity (Strassen 5+5+8).  Joint
    encoder's combined search space (168 bilinear booleans +
    L_total × 24 SLP variables) exceeds framework wedge limit.
    Documented.

**Phase D structural enumeration** — `phase_d_enumerate.py`

  - Z3, 31s–330s per witness.  V.  Enumerated 5 distinct K=7
    ±1 witnesses at Σ\|nz| ≤ 36; ALL FIVE have total SLP = 18.
    Framework-certified statement: "across enumerated ±1 K=7
    bilinear decompositions, minimum total SLP cost = 18".
    L1.2-pattern applied at the SLP-cost level.

### L3.1 — Sorting networks (PARKED)

`benchmarks/open_prbs/sorting_networks/`

**N≤6 known optima** — Z3, 0.03s–65s.  V.  Mechanically
validated at sizes where Codish et al. closed the question.

**N=7 and above** — WEDGE.  Z3's SAT engine doesn't scale for
this large pure-Boolean propagation problem.  MiniSat /
Glucose dominate Z3 on such instances per Codish-Cruz-Filipe
2014 (`STRETCH_STATUS.md` previously noted this; PARKED here
as documented IR validation).

### L3.4 — Branchless code synthesis (PARKED)

`benchmarks/open_prbs/branchless_codegen/`

**HD-recipe rediscoveries (4-bit + 8-bit)** —
`search.py` with various specs.

  - Z3, 0.21s–44s per kernel.  S.  Rediscovered:
    - `abs4 / abs8` at 3 ops (textbook).
    - `sign4` at 4 ops (NON-TEXTBOOK 4-op variant — Z3
      found a different 4-op shape using only SAR + SUB,
      distinct from the textbook `(x >> W-1) | (-x >>u W-1)`).
    - `isnonzero4` at 4 ops (textbook).
    - **`avg4u` at 4 ops (textbook)** — and the framework
      proved C=3 UNSAT in 14.6s.  **First Z3-kernel-checked
      optimality proof for an HD-style branchless kernel.**
      Modest novelty per result but a real Z3-checked claim.

**popcount4 / parity8 — alphabet limit** — WEDGE.  Constants
(CONST_0, CONST_1) and SHR4 added to alphabet; still wedges past
C=5.  PARKED as documented alphabet-reach limit; future work
would author Lean-axiomatized SWAR sub-circuits per the new
CLAUDE.md guiding principle.

### L1.6 — Bipartite matching on interval graphs

`benchmarks/open_prbs/l16_bipartite_matching/`

**Template-class speculation sweep** — `speculate.py`

  - Lean only, ~40s for a 9-pair (3 templates × 3 targets)
    sweep.  V.  Same L1.2-pattern speculation but at the
    cost-bound level.  Enumerates (template, cost-target)
    pairs and queries Lean whether the corresponding cost
    axiom dominates the target.  Result table:
    - T1 Glover ⇒ TGT_LOOSE (N log N + E + 200): VALID.
    - T2 Bucketed ⇒ TGT_LINEAR (N + E + 200): VALID.
    - All other (T_i, TGT_TIGHT = N + E − 1): INVALID.
    Plus contradiction check: trivial Ω(max(N, E)) lower
    bounds DO NOT close TGT_TIGHT (since max(N, E) ≤ N + E).
    So the open question genuinely remains.

**First end-to-end matching benchmark** — `bench_glover_verify.py`

  - Z3 + Lean (📋 1 `.solved.lean` companion, 13 `.failed.lean`
    documenting correctly-rejected subsets).  ~3 min.  S, 1
    solution.
  - Why interesting: first cost-bound graph-flavored benchmark
    synthesizing end-to-end.  τ = `{is_valid_pm(G, n, i, M) == 1,
    0 ≤ i, i ≤ n}`, ϕ = `n − i`, cost@L = `n − i`, cost_target
    = `"n"`.  All obligations close via Lean dispatch + the
    Tier-3 helper that explicitly cites `user_axiom_2` after
    substituting `i = n` from the loop exit.
  - Discoveries along the way: a real cost-* Lean dispatch
    import bug (CostLemmas namespace not imported in the
    generated file), surfaced + fixed.  Generic Lean tactic
    chain doesn't instantiate quantified UFs cleanly without
    helper guidance.
  - **Caveat (load-bearing)**: the matching operations are
    **fully axiomatized via UFs** — `empty_matching` and
    `process_endpoint` are uninterpreted; the algorithm shape
    isn't synthesized.  This validates the cost-invariants
    pipeline on graph-flavored problems but is NOT real
    algorithm discovery.

**Slice B (concrete-operations matching) — closed 2026-05-23.**
Four sub-slices that progressively replace Slice A's UF crutches
with concrete IR operations on `int[][]` adjacency + `int[]`
matching state.

**Slice B.1: bench_pair_consecutive** — `bench_pair_consecutive.py`

  - Z3 + Lean (📋 1 `.solved.lean`).  695s.  S, 1 solution.
  - First concrete-operations matching benchmark to synthesize
    end-to-end.  Template `SB() >> Loop(SB(n=2))`; body pairs
    `(i, i+1)` if `G[i][i+1] >= 1`, advances by 2 otherwise.
    Quantified matching-invariant directly over `M[k]` /
    `G[k][M[k]]` reads — no UFs.
  - τ minimized to `{0 ≤ i, i ≤ n, matching-invariant}`;
    unmatched-tail dropped under conjunctive enumeration.
  - Load-bearing helper `sc2_fallthrough_cb44bbf0.solved.lean`
    (~50 LOC): case-split on `k ∈ {i, i+1, else}` for MI
    preservation under `M' = store(store M i (i+1)) (i+1) i`,
    cites `h_pre_sym` for the G-symmetric `G[i+1][i] = G[i][i+1]`
    fact in the `k = i+1` case.
  - Why interesting: first benchmark to synthesize a matching
    algorithm whose operations and invariants are **concrete**
    — array reads, nested Update, quantified predicates over
    array contents.

**Slice B.2: bench_pair_multi_count** — `bench_pair_multi_count.py`

  - Z3 + Lean (📋 1 `.solved.lean`).  405s.  S, 1 solution.
  - Multi-candidate exploration at the concrete level.  Pool of
    3 candidate body transitions sharing the same template:
    full-pair, asymmetric (`M[i]:=i+1` only), skip.  Each
    proposes its own `(M-update, i-update, c-update)` triple
    where `c: int` is a counter program variable.
  - Discrimination mechanism: invariant `c >= i`.  Each iteration
    advances `i` by 2 — only the full-pair candidate keeps `c`
    in lockstep (+2 per step).  Asymmetric (+1) and skip (+0)
    can't preserve `c >= i`.  Loop exit gives `i >= n - 1`, so
    `c >= i` discharges the post `c >= n - 1`.
  - Outcome: Cand 0 PICKED, Cand 1 + Cand 2 rejected at the
    inductive level.  Concrete-operations analog of Slice A's
    UF-based exploration — same picking mechanism, no UFs.
  - Load-bearing helper `sc1_fallthrough_f16e259e.solved.lean`
    ports the cb44bbf0 proof structure with the new `c >= i`
    atom and `c' = c + 2` transition binder.

**Slice B.3: source emitters for int[][]** — `emit_py`,
`emit_c`, `emit_rust` extended.

  - emit_py: `int[][]` → `list[list[int]]`; 4-arg
    `Update(A, i, j, v)` → `A[i][j] = v`.  Both default mode
    (proof as comments) and `runtime_check=True` mode (proof
    obligations lowered to `synth.proof_runtime` calls).
    Quantified atoms become `all(...)` / `any(...)`
    comprehensions over `range(0, n)` filtered by the antecedent.
  - emit_c: `int[][]` → `int **` (row-pointer array, caller
    allocates `int *G[]`).  4-arg Update → `A[i][j] = v` with
    the same temp-capture pattern as 1D.
  - emit_rust: input-only `int[][]` → `&[&[i64]]`; in-place /
    output-bearing → `&mut [Vec<i64>]` (IndexMut over slice +
    Vec lets `A[i][j] = v` compile cleanly).  Subscript casts
    chain naturally: `G[(i) as usize][(j) as usize]`.
  - Test coverage: `tests/test_emit_c.py:test_matrix_init` and
    `tests/test_emit_rust.py:test_matrix_init` exercise the 4-arg
    Update path end-to-end (synth → emit → compile → run).
    Both suites: 12/12 pass.
  - bench_pair_consecutive's synthesized solution round-trips
    through all three emitters and produces the expected output
    `M = [1, 0, 3, 2]` on a 4-vertex chain graph (verified in
    `scratch/pair_consec_emit_demo.py`).

**Slice B.4: bench_glover_concrete** — Slice A → Slice B
unification — `bench_glover_concrete.py`

  - Z3 + Lean (📋 1 `.solved.lean`).  441s.  S, 1 solution.
  - Same 3-candidate pool as B.2 plus `cost_target = "n"` and
    `cost@L0 = "n - i"`.  First benchmark to validate the
    cost-bound infrastructure (COST_INVS §1–§4) on
    concrete-operations templates.  Same exploration outcome
    as B.2: Cand 0 PICKED, others rejected.
  - The 3 new cost obligations (cost-lb, cost-decrement,
    cost-budget) all close via Z3-LIA — no NIA tax (cost
    stays linear).  Cost composes with the count discrimination
    without interaction; the picked Cand 0 cube satisfies both.
  - Load-bearing helper `sc2_fallthrough_fb5e83c0.solved.lean`
    ports B.2's `sc1_fallthrough_f16e259e` via a single sed
    rename (sc1 → sc2 because cost obligations sort before
    safety in the constraint list, shifting the constraint
    index).  Same case-split + omega proof.
  - Unification claim: multi-candidate exploration + cost-bound
    discrimination works WITHOUT UF crutches.  Slice A's
    discovery mechanism transfers to concrete operations
    cleanly.

**What remains for L1.6 itself**: B.1–B.4 demonstrate concrete
matching operations on chain graphs (pre asserts
`G[k][k+1] >= 1` for all k).  Real L1.6 attack — sub-O(N + E)
on arbitrary bipartite graphs — needs a richer graph IR,
augmenting-path search (multi-week framework extension), and
augmenting-path-free invariants.  Banked as future work.

**Phase K.D — chain-aware nested-loop break (2026-05-25).**
The `_break: True` atom flag now plumbs through to a
chain-aware break-bundle obligation.  Two benchmarks land on
this branch.

**Smoke benchmark — `bench_nested_break_smoke.py`**

  - Z3 only.  0.3s.  S, 1 solution.
  - Outer Loop containing inner Loop with a `_break: True`
    branch; inner break propagates `τ_outer` through frame
    eqs without modifying any state.  Pure framework smoke
    (no graph algorithm content).
  - Validates: chain-aware break-bundle consequent
    (`τ_enclosing(body_out)`), abstract-transition relax
    (`¬g_inner` dropped on the enclosing's body item), and
    Lean translator parity.

**First L1.6 2-nested-loop AP search — `bench_aug3_two_loops.py`**

  - Z3 + Lean (📋 3 Tier-3 helpers).  578s.  S, 1 solution.
    Helpers `k32_2l_inner_entry` (sc1),
    `k32_2l_inner_break` (sc3),
    `k32_2l_outer_body_inductive` (sc7) live in
    `lean/SynthLean/Y2Corpus/l16_aug3_two_loops/Helpers.lean`.
    Each closes via omega + direct hypothesis citations
    (algorithm doesn't modify M; matching-invariant carried
    trivially through frame eqs).
  - Synthesized algorithm (paraphrased):

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

  - **Discoveries**:
      1. **Lean / Z3 obligation parity bug** surfaced and
         fixed (lesson #66).  Chain-aware translator was
         emitting `¬g_inner` for every Loop, including
         break-capable ones; Z3 didn't have that hypothesis
         after K.D.  Soundness gap closed in the same branch.
      2. **Find-flag + increment-at-start idiom** (lesson #67).
         The break primitive only exits the innermost Loop;
         to short-circuit outer iterations on hit, the inner
         branch sets `found := 1` and outer guards include
         `found == 0`.  Increment-at-start keeps the inner
         Loop as the last chain item.  This idiom unlocks
         all "search nested + exit on hit" algorithms within
         the existing framework without new IR primitives.
      3. **Fpre propagation into inner walks** trims
         |τ_outer| from 7 atoms to 3 — input facts no longer
         need to be re-stated as outer τ atoms.
  - **Caveat**: this is the first CONCRETE (non-axiomatized)
    2-nested-loop augmenting-path search to synthesize via
    the framework.

**First L1.6 3-nested-loop AP search — `bench_aug3_three_loops.py`**

  - Z3 + Lean (📋 6 Tier-3 helpers).  1466s.  S, 1 solution.
    Helpers `k32_3l_middle_entry` (sc1),
    `k32_3l_inner_entry` (sc2),
    `k32_3l_inner_break` (sc4),
    `k32_3l_middle_body_ind` (sc8),
    `k32_3l_outer_body_ind` (sc10),
    `k32_3l_final` (sc12 — FLAT-shape signature, see
    discovery #2 below) live in
    `lean/SynthLean/Y2Corpus/l16_aug3_three_loops/Helpers.lean`.
  - First CONCRETE 3-nested-loop augmenting-path search
    (u, v, w all iterated) to synthesize via the framework.
    Validates the find-flag + increment-at-start idiom at
    3-nesting depth.
  - **Discoveries**:
      1. **Find-flag idiom scales to 3-nesting** (lesson #67
         applied at depth 3).  The K.D framework pieces all
         work without modification — remaining cost is purely
         benchmark-level (τ design + 6 Tier-3 helpers).
      2. **FLAT-vs-chain-aware dispatch sharp edge**
         (lesson #69).  At L0 level, `verify.py` dispatches
         chain-bundle-post to `theorem_for_chain_bundle`
         (FLAT — pre-loop vars unprimed, post-loop primed)
         NOT `theorem_for_chain_bundle_chain` when the L0
         chain prefix has no non-SB items.  `k32_3l_final`
         was authored with chain-aware `_sN` binders first;
         the cite failed type-checking until the helper
         signature was reshaped to the FLAT (pre/post) form.
         Banked in problem.skill helper-authoring section.
      3. **Wedge detector caught the missing sc1 helper**
         on the first run (60 dispatches before abandonment;
         `NEEDS-HELPERS` hint pointed straight at it).  The
         second run with the added helper closed in 1466s.
         This is the canonical Phase K.D.W validation point —
         see lesson #68.
  - **Caveat**: the 2-loop and 3-loop AP search benchmarks
    establish that the framework can synthesize concrete
    nested-loop graph algorithms with find-flag short-circuit
    patterns.  L1.6's open question (sub-O(N+E)) survives.

**Slice C (multi-template parallel exploration) — closed
2026-05-23.**  First multi-VARIANT exploration at the TEMPLATE
level via `synth.multi_template.multi_template_solve` (parallel-
subprocess harness, architecture decision recorded in RESEARCH.md
§I).

**Slice C: bench_l16_multi_template** — `bench_l16_multi_template.py`

  - Z3 + Lean (📋 4 `.solved.lean` across 2 variants).
    969s sequential total.  S, exploration table:
    T_A PICK, T_B PICK, T_C REJECT.
  - Three algorithm shapes for the same matching spec on a
    clique-graph precondition.  T_A (linear sweep, 316s,
    score 29.50), T_B (two-pointer, 652s, score 37.50),
    T_C (no-op, 0s — rejected at post-bundle).  Common spec
    has clique pre `G[p][q] >= 1 for all distinct p, q in
    [0, n)` and post `matching-invariant ∧ c >= n - 1`.
  - Why interesting: first benchmark to exercise multi-
    template Cartesian search on real per-variant Tier-3
    helpers.  Validates that the framework picks both valid
    algorithm shapes from a shared spec and correctly rejects
    the no-op.  Each variant runs as an independent
    `Problem` via `ProcessPoolExecutor` — no IR changes,
    soundness story unchanged.
  - Discoveries along the way:
    1. **Architecture decision** (RESEARCH.md §I): user
       pushback rejected the obvious "TemplateUnion IR
       node" approach in favor of parallel subprocess
       harness.  See EXPERIENCE_REPORT.md CS-13.
    2. **Parallel contention** (lesson #61): 3 synth
       subprocesses × ~4 internal Lean workers per saturate
       8-core host; `lake env lean` cache lookups time out
       at 15s under load → spurious unknown verdicts.
       Workaround: `max_workers=1` sequential dispatch.
    3. **T_B ranking spec bug**: phi `right - left` is
       negative at loop exit (where left ≥ right).  Fixed
       to `right - left + 1` and added τ atom
       `left <= right + 1`.  Surfaced ONLY via the
       framework's per-class enumeration — manual
       inspection of the spec wouldn't have caught it
       because the loop guard `left < right` makes
       `right - left > 0` hold WHILE LOOPING.
  - **Caveat**: same as B.1-B.4 — restricted to chain/clique
    graphs with a count-bounded post in place of true
    maximum-matching.  L1.6's open question (sub-O(N+E))
    survives the slice closures.

**Slice 2.C (max matching with CONCRETE IsMatching + Tier-1
proven flip-preservation) — closed 2026-05-27.**  First L1.6
max-matching benchmark to ship with REAL Lean proofs for all
algorithm-step preservation lemmas.  Trust tier reduced from
Slice 2.B's 5 axioms (matching-machinery + Berge + class-
restriction) to only 2 axioms (Berge + class-restriction).
UFs: 4 → 2.

**bench_max_matching_concrete** — `bench_max_matching_concrete.py`

  - Z3 + Lean (🛡️ 9 Tier-1 helpers; 2 axioms).  131.9s.  S,
    1 solution.  Helpers
    `flip_preserves_im` (Tier-1 PROVEN theorem replacing
    Slice 2.B's `mm_flip_preserves_matching` axiom — ~120
    LOC of real Lean proof from first principles),
    `mm_sc1_l0_entry`, `mm_sc2_l1_entry`, `mm_sc3_l2_entry`,
    `mm_sc5_l2_break`, `mm_sc6_l2_safety_step`,
    `mm_sc9_l1_body_ind`, `mm_sc11_l0_body_ind`,
    `mm_sc14_final_berge`, `mm_sc15_coverage`.  Live in
    `lean/SynthLean/Y2Corpus/l16_max_matching_concrete/Helpers.lean`.
  - Algorithm: same as Slice 2.B (3-nested AP search +
    flip + tail-recur), but the printed loop invariants show
    CONCRETE matching predicates (4 separate `ForAll` atoms:
    range / symm / no_self / edge) instead of the
    `IsMatching G n M = 1` UF.
  - **2 UFs (was 4)**: `IsMaxMatching`, `ExistsAugPath`.
    Dropped: `MatchingSize`, `IsMatching`.
  - **2 axioms (was 6)**: `mm_berge` (Berge's classical
    theorem) + `mm_termination_implies_no_ap` (class-
    restriction).  Dropped: `mm_size_nonneg`,
    `mm_size_bounded`, `mm_flip_increases`,
    `mm_flip_preserves_matching` — the last is now a Tier-1
    Lean proof.
  - **Local `c : int`** counter, incremented by 2 per AP-
    flip.  Replaces the `MatchingSize` UF's role.
  - **τ counts inflated**: τ@L0 → 8 atoms (was 4); τ@L1 →
    10; τ@L2 → 12 (= 4 IM atoms + 8 other).  2^12 = 4096
    subsets per L2 safety-check.  Minimal-required-atoms
    helpers (lesson #71/#75) keep the per-subset
    enumeration tractable.
  - **Discoveries**:
      1. **`no_self` atom is load-bearing** (lesson #73).
         Without `M[k] ≠ k` (for matched k), the 3-atom
         predicate admits `M[v] = v`, which breaks the
         flip-preserves-IM proof's case analysis `{u, v, M
         v, w}` distinct.  Discovered while attempting to
         prove `flip_preserves_im` from the 3-atom predicate;
         the proof can't close until `no_self` is added.
         When concretizing a UF + axiom abstraction, audit
         which mathematical properties the UF's axioms
         implicitly assumed.
      2. **FLAT vs chain-aware helper signature dispatch
         splits within a single benchmark** (lesson #74).
         sc1/sc6/sc14/sc15 are FLAT; sc2/sc3/sc9/sc11 are
         chain-aware.  The rule: chain prefix to target has
         only SB items → FLAT; otherwise chain-aware.
         Multiple commits during Slice 2.C closure (`ed43dd3`,
         `830c52c`) were sc1/sc6 helper signature fixes
         after `unknown identifier` errors.  Smoke-test each
         helper individually via `verify_class_via_lean`
         before committing.
      3. **Tier-1 promotion of `flip_preserves_im` from
         Slice 2.B's `mm_flip_preserves_matching` axiom**
         is the load-bearing research win.  ~120 LOC Lean
         proof using pointwise store-unfolding +
         destructuring M's 4 IM atoms.  Establishes
         "axiom-tightening of synthesized algorithms via
         Lean-proved transition-preservation theorems" as a
         tractable research direction.
  - **Caveats**:
      - **Still axiomatized at the top level**:
        `IsMaxMatching` is a UF; Berge's theorem is an
        axiom.  Slice 2.C tightens the algorithm-STEP
        preservation lemmas; the algorithm-LEVEL correctness
        claim (Berge: no-AP at termination ⇒ max-matching)
        remains classical-mathematics-axiom.
      - **k budget workaround still present** (Slice 2.B's
        framework limitation, lesson banked there).
      - **131.9s wall-clock vs Slice 2.B's 102s** (+29%).
        Cost dominated by the larger τ enumeration (12 vs 8
        atoms on τ@L2).
      - L1.6's open question (sub-O(N+E) on interval graphs)
        still untouched — Slice 2.C addresses the *trust*
        side of correctness, not the *cost-bound* side.

**Slice 2.B (first end-to-end recursive maximum-matching
benchmark) — closed 2026-05-25.**  First L1.6 benchmark with a
genuine `IsMaxMatching` post (not count-bounded surrogate),
axiomatized via Berge's theorem.  Validates the framework's
recursive-matching + 4-loop / 4-UF / 6-axiom dispatch path.

**bench_max_matching_recur** — `bench_max_matching_recur.py`

  - Z3 + Lean (📦 8 Tier-3 helpers).  102s.  S, 1 solution.
    Helpers `mm_sc2_l1_entry`, `mm_sc3_l2_entry`,
    `mm_sc5_l2_break` (flip-preserves-IsMatching), `mm_sc6_l2_safety_step`,
    `mm_sc9_l1_body_ind`, `mm_sc11_l0_body_ind`,
    `mm_sc14_final_berge` (cites class-axiom + Berge),
    `mm_sc15_coverage` (minimal-atoms: requires only τ@L0 atom 2)
    live in `lean/SynthLean/Y2Corpus/l16_max_matching_recur/Helpers.lean`.
  - Algorithm: 3-nested AP search (u, v, w loops) + flip on
    found-flag + tail-recur `M := synth(G, n, M, k - 1)`
    with `phi@PROC = k` (explicit iteration budget bounded
    by `n/2`).
  - 4 UFs: `MatchingSize`, `IsMatching`, `IsMaxMatching`,
    `ExistsAugPath`.  6 axioms: matching theory + Berge +
    class-restriction (`mm_termination_implies_no_ap`).
  - **Discoveries**:
      1. **`chain_paths_local` atom_refs preservation bug**
         (lesson #70).  Cartesian-path generator was
         clearing the refs accumulator after first commit, so
         second-path constraints lost their loop_id binding.
         Symptom: helper short-circuit silently skipped sc14
         despite the helper validating in isolation.
         Soundness-adjacent fix: snapshot+restore refs per
         yielded iteration.  (commit d69ce41)
      2. **Solver coverage routing for `loop_id=None`**
         (lesson #72).  Procedure-level multi-branch SB(n>1)
         coverage was gated out of axiom-heavy Lean dispatch
         by the standard `_extract_loop_id(sc) is not None`
         filter.  Two-line carve-out enables Lean dispatch
         for these constraints.  (commit 01f9cb0)
      3. **Minimal-required-atoms helper pattern**
         (lesson #71).  `mm_sc15_coverage` requires only τ@L0
         atom 2 (`found ∈ {0,1}`); per-subset enumeration fires
         the helper on every subset containing atom 2.
         Eliminates 8 partial-subset UNKNOWNs that would
         otherwise sound-mode-reject and cause global SAT
         UNSAT.  (commit 01f9cb0)
      4. **Identity-args tail-recursion framework limit.**
         Natural design (`args.M = M-updated-by-loop`) makes
         `phi(in_b) > phi(args)` shape into `x > x` (always
         false) because in_b binds the loop's post-state, not
         procedure entry.  Workaround: explicit `k: int`
         input with `phi@PROC = k`, `args.k = k - 1`.  Caller
         passes `k = n / 2` as a safe upper bound.
         Principled fix (multi-day, deferred) is tracking
         procedure-entry-state distinctly from in_b in the
         constraint generator.  See SLICE_2B_STATUS.md.
  - **Caveats**:
      - **Axiomatized, not concrete**: `IsMaxMatching` is a
        UF; Berge's theorem is an axiom; `flip-augpath` is
        encoded as a UF + axiom (`flip_preserves_matching`).
        This is NOT algorithm discovery — it validates the
        framework's recursive-matching machinery and the
        4-loop / 4-UF / 6-axiom constraint-dispatch path.
      - **k budget is a framework workaround**, not a
        principled API choice.  The k-input requires the
        caller to know a safe upper bound on iterations (n/2
        for matching).  Tracked in SLICE_2B_STATUS.md.
      - L1.6's open question (sub-O(N+E) maximum matching on
        interval graphs) still survives — Slice 2.B doesn't
        address the cost-bound side, only the correctness side.

### L1.6 breadth push (#246) — interval scheduling + Gale-Shapley

Trio originally scoped as interval_greedy + Gale-Shapley + König.
König scoped out (deferred); 2/3 of the trio landed.  The push
validates that the framework handles structurally-distinct
algorithmic shapes beyond the matching-via-AP-flip template that
Slice 2.B / 2.C closed.

**bench_interval_greedy** — `benchmarks/open_prbs/interval_scheduling/bench_interval_greedy.py`

  - Z3 + Lean (🛡️ 5 Tier-1 PROVEN helpers; 6 step axioms).
    45.1s.  S, 1 solution.  Helpers live in
    `lean/SynthLean/Y2Corpus/interval_greedy/Helpers.lean`.
  - Greedy earliest-deadline-first (EDF) for max non-overlapping
    interval subset.  Template `SB() >> Loop(SB(n=2))` (accept /
    skip body branches).  2 UFs (`GreedyCount`, `GreedyLastEnd`)
    encode the recursive definition of what greedy produces;
    6 axioms cover the base case + accept-step + skip-step.
    Post `count == GreedyCount(S, E, n)`.
  - Why interesting: first L1.6 breadth-push benchmark.
    Validates the recursive-UF *definitional* encoding pattern
    (post asserts equality to the recursively-defined output,
    structural-theory optimality stays out of scope).  All
    per-iteration preservation lemmas proved as Tier-1 theorems
    — zero algorithm-step axioms (only base + step semantics).
  - Caveats: framework verifies that the synthesized algorithm
    IS the greedy, NOT that greedy is optimal (the classical
    exchange argument).  Optimality remains a classical theorem
    that would layer on top.

**bench_gale_shapley** — `benchmarks/open_prbs/stable_matching/bench_gale_shapley.py`

  - Z3 + Lean (🛡️ 6 Tier-1 PROVEN helpers; 17 step axioms).
    86.1s.  S, 1 solution.  V/S = 6/9.  Helpers live in
    `lean/SynthLean/Y2Corpus/gale_shapley/Helpers.lean` (merge
    commit `d5cf825`).
  - Mod-cycled Gale-Shapley stable matching.  Template
    `SB() >> Loop(SB(n=3))` with 3-branch body (SKIP / ACCEPT /
    REJECT) and a `k_left` budget counter from `k_iter`.
    4 UFs declared: `GSMate`, `GSWMate`, `GSNxt`, `GSFreeMan`
    (last one unused, kept in declaration).  17 axioms total:
    3 base (UFs at `k=0`) + 1 structural (`gs_nxt_nonneg`) +
    3 SKIP step + 7 ACCEPT step + 4 REJECT step.  Post is
    recursive-UF equality at `k_iter`.
  - 6 Tier-1 helpers: `gs_sc0_entry_l0` (entry from base axioms);
    `gs_sc1_coverage` (3-way trichotomy on SB(n=3));
    `gs_sc2_skip` (SKIP branch); `gs_sc4_accept` (~170 LOC,
    multi-case proof on the 4-store mate update, cites 7
    ACCEPT step axioms); `gs_sc6_reject` (~80 LOC, mate/wmate
    unchanged via frame eqs, only `nxt[m_cur]` increments);
    `gs_sc9_final` (~15 LOC bridge from loop-exit `k_left' = 0`
    to the bench's `k_iter` post).
  - Why interesting: second L1.6 benchmark with FULL Tier-1
    proven helpers (zero algorithm-step axioms).  Validates the
    recursive-UF step-axiom encoding pattern (Slice 2.C → GS
    generalization) on a non-matching algorithm.  Mod-cycled
    `k_left` budget counter is the standard fix for "no nested
    scan" in iteration-budget algorithms (lesson #77).
  - Discoveries:
    1. **Axiom-free trust as first-class goal** (lesson #76).
       Could have axiomatized per-iteration preservation as
       Tier-2 (3-line axioms per branch); chose Tier-1 theorems
       at substantial extra proof-engineering cost (~170 LOC
       for ACCEPT alone, ~half a day of multi-case proof).
       Win: every algorithm-step claim is verified in Lean
       from concrete `store` semantics + step axioms; trust
       surface is *just* the 17 axioms describing what the
       algorithm does.
    2. **Mod-cycled k_left budget** (lesson #77).  Natural GS
       shape "while ∃ free man, propose" requires a scan or
       queue.  Cycling `m_cur` modulo `n` with `k_left = k_iter`
       reshapes the loop into a single-pass iteration; for
       `k_iter ≥ n²` every (free-man, attempt) pair is visited
       at least once.  Generalizes to any "while X exists, do Y"
       algorithm without a new IR primitive.
    3. **Per-helper required_atoms gating** (lesson #78).  τ@L0
       has 8 atoms (2^8 = 256 subsets per safety obligation).
       Without `required_atoms = frozenset({0..7})` on the
       helper entries, the helper short-circuit only triggers
       on the full subset; smaller subsets fall through to
       generic Lean tactic chain (timeout → UNKNOWN → sound-
       mode rejection → ABANDON).  With full-subset gating,
       the helper cite fires on the full-subset cube alone and
       the synth produces a valid solution carrying full τ —
       score-minimization gives up a small amount but
       correctness lands in 86s instead of wedging.
  - Caveats:
      - Bench's post is recursive-UF equality at `k_iter`, NOT
        GS stability.  The classical "GS produces a stable
        matching" theorem would be a SEPARATE axiom layered on
        top.
      - The unused `GSFreeMan` UF reflects a declaration we
        kept for future stability-property extension.
      - König was scoped out of the trio (deferred); this push
        landed 2/3 of the original task #246 scope.

---

## Stronger discovery moments

Where the atom-subset choice or invariant shape did real work
that a human might not have written by hand:

1. **Bubble sort's bilateral suffix-sorted atom**
   (`∀p,q. q ≥ n−i ⇒ A[p] ≤ A[q]`) — subsumes two seemingly-
   distinct invariants (suffix sorted + prefix dominated by
   suffix) into one quantified atom (lesson #23).

2. **`avg4u` Z3-checked optimality at 4 ops** — Hacker's
   Delight gives `(a & b) + ((a ^ b) >> 1)` for overflow-free
   average; HD doesn't prove it minimal.  Framework's
   exhaustive C≤3 UNSAT in 14.6s + C=4 SAT proves 4 is the
   minimum for the encoded op alphabet.  First Z3-kernel-checked
   minimality for an HD recipe.

3. **L1.2 K=10 + L1.5 SLP=18 structural narratives** — six
   structural classes UNSAT (L1.2) and 5 enumerated witnesses
   all at SLP=18 (L1.5) form Lean-checked impossibility
   narratives across the structurally-distinct algorithm
   shapes our library exposes.  Not algorithm discovery, but
   negative-direction structural results that compose with
   future template additions.

4. **sign4 non-textbook 4-op variant** — Z3 found a 4-op `sign`
   construction using only SAR + SUB, distinct from the
   textbook `(x >> W-1) | (-x >>u W-1)`.  Same op count;
   different shape.

5. **τ atom drop in `nested_zero_array`** — the synthesizer
   picked a MORE minimal τ_inner than the human witness
   (dropping `0 ≤ j`, `i < n` both derivable from antecedent
   path).  Direct evidence that conjunctive τ enumeration
   does real work beyond hand-curation.

---

## What the framework has NOT done

For honesty in self-assessment:

- **No published-OPEN upper bound has been beaten.**  The
  L1.2 / L1.5 / L1.6 work produced structural impossibility
  narratives across enumerated classes; the open frontier
  remains where it was.
- **L1.6 algorithm discovery requires graph IR + matching data
  structures + new operations** — partial progress: Slice B
  (2026-05-23) closed four sub-slices demonstrating concrete
  matching operations + multi-candidate exploration + cost-bound
  discrimination, all without UFs (bench_pair_consecutive,
  bench_pair_multi_count, bench_glover_concrete).  But the
  benchmarks are restricted to chain graphs and use a count-
  bounded post in place of true maximum-matching.  Real L1.6
  attack — sub-O(N + E) on arbitrary bipartite graphs — still
  needs augmenting-path search + augmenting-path-free
  invariants (multi-week extension).
- **Direct rank-1 SAT past ~300 booleans wedges** — observed
  on L2.1 n=5, L1.2 K=10, L1.5 threshold-35, L3.1 sorting
  N≥7, L3.4 joint encoder.  Documented as the framework's
  reach limit.
- **Pure-Boolean propagation SAT** is the wrong shape for
  Z3 — sorting networks confirmed this.  MiniSat / Glucose
  would dominate.

---

## Cross-references

- `OPEN_PRBS.md` — catalog of open problems and framework match.
- `COST_INVS.md` — resource-bound invariants design + status.
- `SOUNDNESS.md` — soundness posture per constraint kind.
- `CLAUDE.md` — full implementation history + encoding lessons.
- `EXPERIENCE_REPORT.md` — case studies on the partnership.
