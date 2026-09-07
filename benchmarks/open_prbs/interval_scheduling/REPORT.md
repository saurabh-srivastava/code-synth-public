# Interval scheduling — greedy EDF max non-overlapping subset

Given `n` intervals `[S[i], E[i])` sorted by end-time, find the
maximum number of pairwise non-overlapping intervals.  The
classical algorithm is **greedy earliest-deadline-first (EDF)**:
iterate sorted intervals; accept each interval whose start is
≥ the last accepted interval's end; reject otherwise.

```
i := 0
count := 0
last_end := -1
while i < n:
    if S[i] >= last_end:
        last_end := E[i]
        count := count + 1
        i := i + 1
    else:
        i := i + 1
return count
```

## Context

First of the **L1.6 BREADTH push trio** (task #246) — interval
scheduling + Gale-Shapley stable matching + König vertex cover.
Each validates that the framework handles a structurally
distinct algorithmic shape beyond the matching-via-AP-flip
template that Slice 2.B / 2.C closed:

  - **Interval scheduling** (this benchmark) — greedy on
    sorted input with a recursive optimality definition.
  - **Gale-Shapley** — stable matching via deferred-acceptance
    proposal/rejection loop.
  - **König** — reuses Slice 2.C's matching substrate to build
    a minimum vertex cover from a maximum matching.

The trio establishes breadth of algorithm-shape coverage on
top of the L1.6 substrate (sparse IR + concrete graph
operations + Tier-1 matching theorems).

## Synth

`bench_interval_greedy.py` — 45.1s wall, 1 verified solution
(commit `203cafb`).  **5 Tier-1 helpers** in
`lean/SynthLean/Y2Corpus/interval_greedy/Helpers.lean`.

## Spec design

The framework verifies that the synthesized algorithm IS the
greedy — NOT that greedy is optimal.  Optimality of greedy EDF
is the classical exchange argument; we encode it as the
recursive *definition* of what greedy produces (via UFs) and let
the synth match its loop against that definition.  This is the
same posture as Slice 2.B's Berge treatment: structural theory
stays in axioms, algorithmic correctness gets verified.

**2 UFs** encode the recursive definition:

  | UF | Signature | Meaning |
  | --- | --- | --- |
  | `GreedyCount`    | `(int[], int[], int) → int` | count after processing first n intervals |
  | `GreedyLastEnd`  | `(int[], int[], int) → int` | last accepted deadline after n iters |

**6 axioms** encode the base case + accept-step + skip-step:

  - **A1 (×2 — base)**:  `GreedyCount(S, E, 0) = 0`,
    `GreedyLastEnd(S, E, 0) = -1`.
  - **A2 (×2 — accept)**:  if `S[i] ≥ GreedyLastEnd(...,i)` then
    `GreedyCount(...,i+1) = GreedyCount(...,i) + 1` and
    `GreedyLastEnd(...,i+1) = E[i]`.
  - **A3 (×2 — skip)**:  if `S[i] < GreedyLastEnd(...,i)` then
    `GreedyCount(...,i+1) = GreedyCount(...,i)` and
    `GreedyLastEnd(...,i+1) = GreedyLastEnd(...,i)`.

**Post**: `count == GreedyCount(S, E, n)`.

**Pre**: `n ≥ 0`, end-times sorted (`∀ k1 < k2 < n, E[k1] ≤
E[k2]`), and each interval valid (`0 ≤ S[k] < E[k]`).

**τ@L0 — 5 atoms** encoding the loop invariant:

  | # | Atom | Role |
  | --- | --- | --- |
  | 0 | `0 ≤ i`                                | i bounds (lower) |
  | 1 | `i ≤ n`                                | i bounds (upper) |
  | 2 | `0 ≤ count`                            | count non-neg |
  | 3 | `count == GreedyCount(S, E, i)`        | counter matches definition |
  | 4 | `last_end == GreedyLastEnd(S, E, i)`   | last-end matches definition |

**ϕ@L0 = `n - i`**, the standard linear ranking.

The two "matches-greedy" atoms (3, 4) are load-bearing: they
let the per-branch inductive cite the accept-step / skip-step
axioms directly (the framework's translator emits the branch
guard as a hypothesis named `h_guard`, which matches the
axiom's antecedent shape).

## Helpers

5 Tier-1 helpers in `Helpers.lean` (all ~10-25 LOC proofs):

  | Helper | Constraint | Proof sketch |
  | --- | --- | --- |
  | `is_sc_entry_l0`  | sc0 — L0 entry-bundle after B0 init | `subst` the 3 init transitions; cite A1 (base case) for atoms 3 and 4. |
  | `is_sc_accept`    | sc — body branch 0 (accept)         | Destructure τ; cite A2 with `h_guard` to extend GreedyCount and GreedyLastEnd. |
  | `is_sc_skip`      | sc — body branch 1 (skip)           | Destructure τ; cite A3 with `h_guard` to preserve both UFs. |
  | `is_sc_coverage`  | coverage — SB(n=2) loop body        | `h_g_loop` gives `i < n`; `S[i] ≥ last_end` vs `S[i] < last_end` covers by trichotomy via `omega`. |
  | `is_sc_final`     | sc — L0 final bundle (post)         | `¬g` + τ atom 1 gives `i = n`; combined with τ atom 3 gives `count = GreedyCount(S, E, n)`. |

All five helpers cite axioms directly — no Tier-3 axioms beyond
the user-supplied A1-A3.

## Honest framing

This is the **recursive-greedy pattern**: a greedy algorithm
whose correctness is captured by treating the greedy's own
output as a recursively-defined function on the input, then
verifying the algorithm's loop matches that recursion
step-for-step.  The framework verifies "this algorithm computes
GreedyCount(S, E, n)"; optimality of GreedyCount is encoded as
the axioms A1-A3 (which IS the algorithm's specification —
trivially true by definition).

A separate proof that greedy EDF is OPTIMAL (no scheduling
algorithm produces a larger count) is the classical exchange
argument; we don't attempt it here.  Same boundary as Slice
2.B's Berge: the framework gets concrete-operations algorithm
synthesis; classical-theory facts ride on top as axioms.

The pattern generalizes to other recursive-greedy algorithms
(Huffman coding, activity-selection variants, matroid-greedy)
where a "produced-by-greedy" UF + accept/reject axioms captures
the per-step behavior.

## What's next

  - **König vertex cover** — reuses Slice 2.C's matching
    substrate.  Build minimum vertex cover from a maximum
    matching via the König–Egerváry construction.  Expected
    to be cheap (matching substrate already in place; König
    is a one-pass post-processing step).
  - **Gale-Shapley stable matching** — proposal/rejection
    deferred-acceptance.  Structurally distinct: two-sided
    preferences, mutual loop over proposers and receivers.
    Tests that the framework handles the deferred-acceptance
    pattern beyond AP-flip.

Both targeted as 1-2 day benchmarks on top of the existing
substrate.

## Sources

  - `bench_interval_greedy.py` — benchmark spec.
  - `lean/SynthLean/Y2Corpus/interval_greedy/Helpers.lean` —
    5 Tier-1 helpers.
