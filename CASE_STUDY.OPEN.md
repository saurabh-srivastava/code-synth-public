# Case study — toward maximum matching (the open frontier)

An addendum to `CASE_STUDY.md`.  Where the greedy-match
benchmark showed the framework synthesizing a *real graph
algorithm* (greedy maximal matching) end-to-end, this case
study traces the *next step beyond it*: maximum matching via
Berge's theorem.  The benchmark is
`benchmarks/open_prbs/l16_bipartite_matching/bench_aug_path_max.py`
(C1.D K.3.0).  K.3.0 is the first milestone in C1.D's
multi-step plan; K.3.2 (concrete augmenting-path detection)
is sketched but not yet implemented.

This document covers:
  1. What max-matching means and why it's harder.
  2. Berge's theorem as the bridge.
  3. The K.3.0 benchmark — Slice A pattern at the
     algorithm-level.
  4. The unsolved bits — design for K.3.2+ and where the open
     question lives.

If you haven't read `CASE_STUDY.md` yet, do that first — this
addendum assumes familiarity with the framework's pipeline
(template + atoms → constraints → Z3/Lean → synthesized
program).

---

## 1.  What changed from CASE_STUDY.md

| | CASE_STUDY.md (greedy maximal)        | This (K.3.0 maximum) |
| --- | --- | --- |
| Spec class | Maximal matching | Maximum matching |
| Graph    | Arbitrary edge list (sparse)         | Any (axiomatized) |
| Algorithm | Iterates edges, pairs unmatched      | Iterates AP flips |
| Body op  | Concrete `Update(Update(M, u, v), v, u)` | UF `step_augment(G, n, M)` |
| Synth picks | Loop guard + ranking + transitions   | Loop guard + ranking + (UF) transition |
| Tier-3 helpers | 2 (sc2 inductive, sc7 post)       | 0 — generic chain closes everything |
| Wall time | 864s                                  | 15s |

The difference is the spec strength.  Maximal matching ("no
edge has both endpoints unmatched") is a *local* property —
checked edge-by-edge.  Maximum matching ("|M| is the largest
possible") is *global* — defined over all possible matchings.

The framework can't directly check "|M| is the largest" without
either enumerating all matchings (exponential) or appealing to a
characterization theorem.  **Berge's theorem is that
characterization.**

---

## 2.  Berge's theorem — the bridge

**Theorem (Berge, 1957)**: A matching M in a graph G is
*maximum* iff there is no *augmenting path* in G wrt M, where
an *augmenting path* is a simple path whose endpoints are
unmatched and whose edges alternate between G \\ M and M.

The forward direction (the one we need) gives:

> If you have a valid matching M and there is no AP, then M
> is maximum.

In the synthesizer, this becomes an *axiom* in the user's
Problem:

```python
axioms = [
    # (A6) Berge forward:
    "ForAll(lambda G_, n_, M_: Implies("
    "is_matching(G_, n_, M_) == 1 and "
    "not (exists_aug_path(G_, n_, M_) == 1), "
    "is_max_matching(G_, n_, M_) == 1))",
    ...
]
```

The synth framework's post-bundle obligation says:
*"at loop exit, given τ + ¬g, the user's post must hold."*

With:
  - τ = `is_matching(G, n, M) == 1`,
  - ¬g = `¬(exists_aug_path(G, n, M) == 1)`,
  - post = `is_max_matching(G, n, M) == 1`,

…the obligation reduces to applying A6.  Lean's `aesop` finds
this in milliseconds.

### 2.1  The Int-valued-bool gap

A subtle bug surfaced during the first synth attempt: Berge
was originally phrased as `... and exists_aug_path == 0 →
is_max ...`.  The synth framework's loop-exit form is
`¬(exists_aug_path == 1)`.

For Int-valued UFs, `¬(x == 1)` does NOT imply `x == 0` —
the UF could return 2, -1, or anything else.  Lean's `aesop`
correctly refused to bridge.

Fix: restate Berge as `... and not (exists_aug_path == 1)
→ is_max ...`.  Now matches h_not_g directly.  Lesson banked:
**when an axiom is meant to close a loop-exit obligation,
match the framework's `¬(guard == 1)` form exactly**.

---

## 3.  The K.3.0 benchmark — Slice A at the algorithm level

The benchmark's full setup:

```python
PROBLEM = Problem(
    template = SB() >> Loop(SB()),
    inputs   = [Var("G", "int", "input"), Var("n", "int", "input")],
    outputs  = [Var("M", "int", "output")],
    locals   = [],   # no local counter — phi uses a UF
    uninterpreted = [
        ("is_matching",     ["int", "int", "int"], "int"),
        ("is_max_matching", ["int", "int", "int"], "int"),
        ("exists_aug_path", ["int", "int", "int"], "int"),
        ("matching_size",   ["int", "int", "int"], "int"),
        ("empty_matching",  [],                    "int"),
        ("step_augment",    ["int", "int", "int"], "int"),
    ],
    axioms = [
        # A1: empty_matching is a valid matching.
        # A2: matching_size >= 0.
        # A3: is_matching → 2*matching_size <= n.
        # A4: step_augment preserves is_matching.
        # A5: step_augment increments matching_size by 1.
        # A6: Berge — is_matching ∧ ¬(exists_aug_path==1) → is_max_matching.
    ],
    pre  = "n >= 0",
    post = "is_max_matching(G, n, M) == 1",
    atoms = {
        "s@B0":   [{"M": "empty_matching()"}],
        "tau@L0": ["is_matching(G, n, M) == 1"],
        "g@L0":   ["exists_aug_path(G, n, M) == 1"],
        "phi@L0": ["n - 2 * matching_size(G, n, M)"],
        "s@B1":   [{"M": "step_augment(G, n, M)"}],
    },
)
```

Six UFs, six axioms, one τ atom, one guard, one transition.
Minimal.

### 3.1  How the constraints close

The framework generates 5 safety constraints; here's what each
needs from the axiom chain:

| sc | Kind | What it needs | Axiom |
| --- | --- | --- | --- |
| sc0 | safety-bundle-entry | After init (M = empty), τ holds. | A1 (empty is matching). |
| sc1 | safety (inductive) | τ + g + body trans → τ′. After body, M' = step_augment(M); needs is_matching(M') = 1. | A4 (step preserves matching). |
| sc2 | ranking-decrease | phi(in) > phi(out) for body. With phi = n - 2·matching_size(M) and M' = step_augment(M): need ms(M') > ms(M). | A5 (step increments ms by 1). |
| sc3 | ranking-lb    | τ → phi ≥ 0.  Need 2·ms(M) ≤ n. | A3 (matching-size bounded). |
| sc4 | safety-bundle-post | τ + ¬g → post.  Need is_max_matching. | A6 (Berge). |

Every constraint discharges directly via one axiom application
plus omega (for the arithmetic glue).  No Tier-3 helpers
needed — the framework's generic Lean tactic chain handles it
in 15s total wall.

### 3.2  Why no local counter

An earlier draft had `locals = [Var("i", "int", "local")]` with
τ atom `2*i ≤ n` and phi `n - 2*i`.  This UNSAT'd.

The issue: `2*i ≤ n` isn't preserved by `i += 1` without
external bounds.  From τ alone, `2*(i+1) ≤ n` requires
`2*i ≤ n - 2`, which is strictly stronger than `2*i ≤ n`.

Fix: drop `i` entirely.  Use phi = `n - 2·matching_size(M)`
directly.  The framework's ranking-lb and ranking-decrease
obligations dispatch to the UF axioms (A3 and A5) without
needing a separate counter.

Lesson: when termination depends on a UF property (here:
matching size grows per iteration, bounded by n/2), encode the
ranking directly in terms of the UF rather than maintaining a
shadow counter that needs its own invariants.

---

## 4.  The synthesized result

```c
int synth(int G, int n) {
    int M;
    M := empty_matching();
    while (exists_aug_path(G, n, M) == 1)
        // [τ = is_matching(G, n, M) == 1
        //  ϕ = n - 2 * matching_size(G, n, M)]
    {
        M := step_augment(G, n, M);
    }
    return M;
}

// Proof obligations:
//   sc0 (entry):   A1 closes.
//   sc1 (induct):  A4 closes.
//   sc2 (rk-dec):  A5 closes.
//   sc3 (rk-lb):   A3 closes.
//   sc4 (post):    A6 (Berge) closes.
```

This is the Edmonds-Karp / Hopcroft-Karp *outer loop shape* —
verified as a maximum-matching algorithm modulo the UFs being
honest implementations of "find AP" and "apply AP".  Berge
makes the verification possible without enumerating matchings.

---

## 5.  What K.3.0 does NOT do — the open frontier

K.3.0 demonstrates the framework can EXPRESS the maximum-
matching spec and verify an outer-loop algorithm against it.
But the algorithm depends on `step_augment` and
`exists_aug_path` being UFs.  Replacing those with concrete
implementations is the open frontier.

### 5.1  K.3.1 — length-1 audit (subsumed by greedy)

A length-1 AP = a single edge with both endpoints unmatched.
"No length-1 AP exists" is exactly the maximal-matching
condition.  bench_greedy_match_general (CASE_STUDY.md) already
synthesizes an algorithm achieving this.  K.3.1 wouldn't add
new framework capability.

### 5.2  K.3.2 — length-3 concrete AP detection (multi-day)

A length-3 AP in bipartite: `u → v → z → w` where:
  - u, w unmatched.
  - (u, v), (z, w) are non-M edges.
  - (v, z) is an M edge (so z = M[v]).

To find and flip: triple-nested loop with breaks (or a
fixed-point iteration with a `made_progress` flag).

```python
made_progress := true
while made_progress:
    made_progress := false
    for u in 0..n:
        if M[u] == -1:
            for v in 0..n:
                if v != u and G[u][v] and M[v] != -1:
                    z := M[v]
                    for w in 0..n:
                        if w != u and w != v and w != z and \
                           M[w] == -1 and G[z][w]:
                            // flip: M[u]=v, M[v]=u, M[z]=w, M[w]=z
                            made_progress := true
                            break  # back to outer-outer
                # break (v loop)
        # break (u loop)
```

Template shape:
  `SB() >> Loop(SB() >> Loop(SB() >> Loop(SB(n=2)) >> SB(n=2)) >> SB(n=2))`

Four levels of loop nesting with multi-branch SBs and
"early-exit" semantics via the made_progress flag.  Each
inner loop becomes a Tier-3 helper task with multiple
constraints — the inductive on the inner loop will have
quantified atoms over the matching state, similar to
bench_greedy_match_general's `h_extend` lemma but composed
across 3-4 loop levels.

Estimated effort: ~1 week for the template authoring +
helper authoring.  Probably another week of debugging the
Lean proofs.

### 5.3  K.3.3 — general-length AP via BFS/DFS (multi-week)

Length-bounded APs (3, 5, 7, ...) saturate the matching only
in graph classes with limited augmenting-path length.  Full
maximum-matching for arbitrary bipartite graphs needs
unbounded-length AP search via BFS or DFS.

This needs IR primitives the framework doesn't have:
  - **Variable-length path storage.**  An int[] of length
    ≤ n suffices, but with a length counter and sentinels.
  - **Visited/parent arrays.**  int[] indicators.
  - **State machine for alternation.**  Track whether the
    next edge to explore should be in M or not.
  - **Path-flip primitive.**  Walk the path array, toggling
    matched/unmatched edges.

Each is implementable as `int[]` machinery, but composing
them into a verified BFS is multi-week.

### 5.4  K.3.4 — Hopcroft-Karp's layered BFS (research-engineering)

Hopcroft-Karp achieves O(E·√V) by finding all length-k APs
in one BFS phase, then length-(k+2), etc.  The "layered"
construction is the key trick.  Multi-week research-
engineering even with K.3.3 substrate.

### 5.5  Sub-O(N+E) on restricted classes (the open question)

Even with K.3.4 implemented, hitting *sub*-O(N+E) on
restricted graph classes (interval graphs, planar, bounded-
treewidth) is a research result.  The framework + Lean lets
us VERIFY a candidate algorithm; the algorithm itself needs
to exist in the mathematical sense first.

Possible angles:
  - **Approximation algorithms** with sub-linear time and
    bounded approximation ratio.
  - **Randomized algorithms** with sub-linear expected time.
  - **Structural-exploit algorithms** that read a sub-linear
    portion of the input under specific graph-class
    invariants.

K.3.0 is the foundation: we can EXPRESS the maximum-matching
goal.  K.3.2-4 builds the substrate.  Beyond that is research.

---

## 6.  Pattern catalog — what the K.3.0 push teaches

### 6.1  UF-axiomatic intermediates buy real expressive power

Slice A's UF-based exploration (CS file `bench_glover_explore`)
demonstrated multi-candidate body-level search.  K.3.0 extends
this to the outer loop's TERMINATION + correctness via UF
ranking (`matching_size`) and a characterization theorem
(Berge).

Pattern: when the goal is a global property (max, min, optimal
under some criterion), use a UF + axiomatic characterization
theorem as the synthesizer-side bridge.  The CONCRETE
implementation of the UF can be added later as a separate
benchmark (Slice A → Slice B unification pattern from B.4).

### 6.2  Match the framework's exit form when stating axioms

Lean's quantifier instantiation didn't bridge `¬(x == 1) ↔
x == 0` for Int-valued UFs.  Restating the axiom in the
`¬(...==1)` form solved it.  Cost: zero.  Time saved:
1 synth iteration.

Pattern: when an axiom is meant to close a loop-exit
obligation, match the framework's `¬(guard)` form exactly.
Don't rely on Lean's solver to perform Int-bool conversions
that aren't axiomatized.

### 6.3  UF-backed ranking beats shadow counters

The first K.3.0 draft used a local `i` counter with invariant
`2*i ≤ n`.  This UNSAT'd because the invariant isn't preserved
by `i += 1` without external bounds.

Fix: phi = `n - 2 * matching_size(G, n, M)`.  The framework
dispatches ranking-lb via the matching-size-bounded axiom and
ranking-decrease via the matching-size-increment axiom.  No
shadow counter needed.

Pattern: encode the ranking directly in UF terms when
termination depends on a UF property.  The "natural"
counter-based form often runs into preservation gaps.

---

## 7.  Where to go next

  **In the codebase**:
  - `benchmarks/open_prbs/l16_bipartite_matching/bench_aug_path_max.py` —
    K.3.0 benchmark.
  - `lean/SynthLean/Matching.lean` — Berge axiom +
    AP predicate (the Prop-level versions; the synth
    side uses Int-valued UFs in the user's `axioms`).
  - `RESEARCH.md §K` — full C1.D plan including K.3.2-4.
  - `benchmarks/open_prbs/l16_bipartite_matching/REPORT.md` —
    L1.6 status with C1.A-C tracker.

  **As research directions**:
  - **K.3.2 (length-3 concrete)** — the next meaningful
    capability bump.  Multi-day.  Would prove the framework
    can synthesize "improve a given matching by short AP
    flips."
  - **K.3.3+ (general-length AP)** — multi-week.  Requires
    new IR primitives (path-storage, visited arrays,
    alternation state machine).
  - **Sub-O(N+E)** — research-scale.  Substrate would help;
    the algorithm itself is the open part.

---

## 8.  Status snapshot

| Piece | Status | Document |
| --- | --- | --- |
| Concrete graph operations | ✓ Slice B | `BENCHMARKS.STATUS.md` |
| Cost-bound infrastructure | ✓ B.4 / COST_INVS §5 | `COST_INVS.md` |
| Multi-template exploration | ✓ Slice C | `REPORT.md` |
| Sparse graph IR (edge list) | ✓ C1.A | `CASE_STUDY.md` |
| Maximal-matching post | ✓ C1.B | `CASE_STUDY.md` |
| Greedy matching synth E2E | ✓ C1.C | `CASE_STUDY.md` |
| **Maximum-matching post (Berge)** | ✓ **K.3.0** | **(this doc)** |
| AP detection (concrete length-3) | ❌ K.3.2 | `RESEARCH.md §K` |
| AP search (general length) | ❌ K.3.3 | `RESEARCH.md §K` |
| Hopcroft-Karp's layered BFS | ❌ K.3.4 | `RESEARCH.md §K` |
| Sub-O(N+E) on restricted classes | ❌ open question | `OPEN_PRBS.md` |

K.3.0 brings the framework to the point where the
maximum-matching SPEC is expressible and verifiable.  The
remaining pieces are concrete algorithm engineering plus the
genuinely open question on sub-O(N+E).
