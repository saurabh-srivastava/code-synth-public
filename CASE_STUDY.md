# Case study — greedy maximal bipartite matching

A self-contained walkthrough of how the synthesizer takes a
*specification* of greedy maximal bipartite matching and
produces a *verified program* — what goes in, what gets
searched, who proves what, what comes out.  The benchmark is
`benchmarks/open_prbs/l16_bipartite_matching/bench_greedy_match_general.py`,
the first L1.6 benchmark to operate on an unstructured graph
with a textbook correctness post.

---

## 1.  The problem

**English**: Given a bipartite graph as an edge list, produce a
matching `M` (each vertex matched to at most one partner) such
that no edge has both endpoints unmatched.  That's the textbook
definition of a *maximal* matching.

**Algorithm we expect the synthesizer to find** (greedy):

```
i := 0
while i < m:
    let u = edges[2*i], v = edges[2*i+1]
    if M[u] == -1 ∧ M[v] == -1:
        M[u], M[v] := v, u
    i := i + 1
```

For each edge in order, pair its endpoints if both are
currently unmatched.  Maximal because once you can't extend,
no edge has two unmatched endpoints by construction.  *Not*
maximum — greedy can miss matchings of larger total size — but
maximal is a real correctness criterion.

---

## 2.  Inputs to synthesis

The synthesizer takes a single Python object:

```python
PROBLEM = Problem(
    template = SB() >> Loop(SB(n=2)),
    inputs   = [Var("edges", "int[]", "input"),
                Var("m",     "int",   "input"),
                Var("n",     "int",   "input"),
                Var("M",     "int[]", "input")],
    outputs  = [Var("M", "int[]", "output")],
    locals   = [Var("i", "int",   "local")],
    axioms   = ["0 == 0"],
    pre      = (
        "n >= 0 and m >= 0 and "
        "ForAll(lambda k: Implies(0 <= k and k < n, M[k] == -1)) and "
        "ForAll(lambda j: Implies("
        "0 <= j and j < m, "
        "0 <= edges[2*j] and edges[2*j] < n and "
        "0 <= edges[2*j + 1] and edges[2*j + 1] < n and "
        "edges[2*j] != edges[2*j + 1]))"
    ),
    post = (
        "ForAll(lambda k: Implies("
        "0 <= k and k < n and M[k] != -1, "
        "0 <= M[k] and M[k] < n)) and "
        "ForAll(lambda j: Implies("
        "0 <= j and j < m, "
        "not (M[edges[2*j]] == -1 and M[edges[2*j + 1]] == -1)))"
    ),
    atoms = {
        "s@B0": [{"i": "0"}],
        "tau@L0": [
            "0 <= i",
            "i <= m",
            "ForAll(lambda k: Implies(0 <= k and k < n and M[k] != -1, "
                              "0 <= M[k] and M[k] < n))",
            "ForAll(lambda j: Implies(0 <= j and j < i, "
                              "not (M[edges[2*j]] == -1 and "
                              "M[edges[2*j + 1]] == -1)))",
        ],
        "g@L0":   ["i < m"],
        "phi@L0": ["m - i"],
        "g@B1.0": ["M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1"],
        "s@B1.0": [{"M": ("Update(Update(M, edges[2*i], edges[2*i + 1]), "
                          "edges[2*i + 1], edges[2*i])"),
                    "i": "i + 1"}],
        "g@B1.1": ["not (M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1)"],
        "s@B1.1": [{"i": "i + 1"}],
    },
)
```

Two pieces deserve unpacking:

### 2.1  The template

```
SB() >> Loop(SB(n=2))
```

This is a *control-flow scaffold* with holes.  Reading left to
right:

  - **`SB()`** — Sequential Block.  An initialization block;
    by convention, the first one.  Holes: `s@B0`.
  - **`Loop(...)`** — A while-loop.  Holes: `tau@L0` (the loop
    invariant), `g@L0` (the loop guard), `phi@L0` (the ranking
    function).
  - **`SB(n=2)`** — Sequential Block with TWO branches.  Each
    branch has its own guard + transition.  Holes: `g@B1.0`,
    `s@B1.0`, `g@B1.1`, `s@B1.1`.  Coverage obligation
    (`⋁ guards ≡ true`) is automatic.

The template is the algorithm's *shape*; the holes are the
DETAILS the synthesizer fills in.

### 2.2  The atom dictionary

`atoms` is a dictionary keyed by hole-id; each value is a list
of *candidate values* for that hole.

  - **`tau@L0`** (the loop invariant) is *conjunctive*: any
    subset of the 4 listed atoms can be picked.  The
    synthesizer's job for this hole is to find a minimal subset
    that proves all the loop's obligations.
  - **Every other hole** is *single-hot*: exactly one candidate
    is picked.  Here each hole has only one candidate, so the
    framework doesn't really get a choice — the search is
    effectively just over τ subsets.

The atom dictionary defines the *search space*.  For this
benchmark: `2^4 = 16` possible τ assignments × `1^8 = 1`
non-τ assignment = `16` candidate programs.

The framework's job is to pick one that proves every safety
constraint.

---

## 3.  Constraint generation

The synthesizer's first phase (`synth.constraints.generate`)
walks the template and emits *safety constraints*.  For our
template, it produces **8 constraints**:

| # | Kind | Roughly what it says |
| --- | --- | --- |
| sc0 | `safety-bundle-entry`  | At loop entry (after `s@B0`), τ holds. |
| sc1 | `safety-bundle-post`   | At loop exit (¬g + τ), the user's `post` holds. |
| sc2 | `safety`               | Body branch 0 preserves τ. |
| sc3 | `coverage`             | The two branch guards cover all cases. |
| sc4 | `safety`               | Body branch 1 preserves τ. |
| sc5 | `ranking-decrease`     | Branch 0's body decreases ϕ. |
| sc6 | `ranking-decrease`     | Branch 1's body decreases ϕ. |
| sc7 | `ranking-lb`           | τ ⇒ ϕ ≥ 0. |

(Indices are constraint-system order; the precise numbering
varies as you add/remove constraint kinds, but the shape is the
above.)

Each safety constraint carries an `atom_refs` list pointing at
which τ atoms appear in its body, and at which *position*
(antecedent or consequent).  This enables the PLDI'09
attribute-class reduction we describe next.

---

## 4.  The search — PLDI'09 attribute-class reduction

For each safety constraint, the framework enumerates every
possible τ subset and asks: *does this subset make the
constraint valid?*

A subset is a *cube* over the τ indicator variables:
`b_τ_0 = T ∧ b_τ_1 = F ∧ ...`.  The framework calls the
verifier on the cube; the verifier returns valid / invalid /
unknown.  Each constraint accumulates a *valid-cubes set* —
the disjunction of cubes that proves it.

The main SAT then asks: *is there an assignment of indicators
(a global τ subset + single-hot picks for other holes) such
that every constraint has at least one valid cube whose literals
all match the assignment?*  If yes, the assignment is a
synthesized solution.

For 4 τ atoms × 8 constraints, that's 4·8 = 32 max
per-constraint enumeration cubes; in practice each constraint
only mentions a subset of τ atoms in its body, so the actual
per-constraint enumeration is smaller.  The framework
hits 354 Lean dispatches over the run.

---

## 5.  The solvers — who proves what

Per safety constraint, the framework dispatches to one of two
solvers:

### 5.1  Z3 — the SMT solver

For most constraint kinds (`safety`, `safety-bundle-entry`,
`safety-bundle-post`, `coverage`, `ranking-*`), the framework
first translates the obligation into Z3's quantifier-free
arithmetic + array theory and asks for *un*-satisfiability of
the negation (which means the obligation is valid).

  - For *linear*-arithmetic obligations (ranking-lb, ranking-
    decrease, simple guards), Z3 closes in milliseconds.
  - For *quantified-array* obligations (anything with `ForAll`
    over array reads), Z3's quantifier-instantiation
    heuristics can return UNKNOWN or worse, false-SAT.

The benchmark's `axioms = ["0 == 0"]` is a deliberate trip-wire:
when `Problem.axioms` is non-empty, the framework routes
safety-* kinds through Lean instead of Z3, sidestepping Z3's
unreliable quantifier reasoning.  The dummy axiom triggers
"axiom-heavy" dispatch.

### 5.2  Lean — the proof assistant

For axiom-heavy kinds (and for any obligation Z3 returns
UNKNOWN on), the framework emits a Lean theorem with a generic
tactic chain:

```
subst_eqs
refine ⟨?_, ?_, ?_, ?_⟩
all_goals (first | assumption | omega | nlinarith
           | (simp_all [store]; done)
           | (aesop; done)
           | ...)
```

Lean's `omega` (linear arithmetic), `nlinarith` (nonlinear),
`aesop` (general proof search), and `simp_all` (rewriting) try
in sequence.  If one closes the goal, the cube is valid.
Otherwise, Lean returns "unknown" — the proof didn't close in
the 15s budget.

### 5.3  Tier-3 helpers — when the generic chain isn't enough

When the generic chain can't close a load-bearing cube — and
the cube IS valid (we just can't prove it with `aesop`) — we
author a *Tier-3 helper*: a `.solved.lean` file containing the
same theorem signature with a hand-written proof.

The framework finds these via *signature-hash filename*:
when verify emits a `.failed.lean` for a hash-X obligation, a
human can author `.solved.lean` at the same hash.  Subsequent
synth runs see the file, type-check it, and treat the cube as
valid.

This benchmark needed **two** Tier-3 helpers.

---

## 6.  The two Tier-3 helpers

### 6.1  `sc2_fallthrough_d7bbb079.solved.lean` — the inductive

The hardest obligation: branch-0 of the body (pair them)
preserves τ at the next iteration.

**Goal** (after substitution): given τ holds with all 4 atoms
(`0 ≤ i, i ≤ m, MI(M), maximal-up-to-i(M)`), the branch-0
guard fires (both endpoints unmatched), and the transition is
applied, show τ holds at `i' = i + 1, M' = store(store M eu
ev) ev eu` where `eu = edges(2i)`, `ev = edges(2i+1)`.

**Proof structure** (~80 lines, full text in
`lean/SynthLean/Y2Corpus/l16_greedy_match_general/sc2_fallthrough_d7bbb079.solved.lean`):

```lean
set_option maxHeartbeats 400000 in   -- default 200k errors here
theorem sc2_fallthrough ... := by
  obtain ⟨h_pre_n, h_pre_m, h_pre_init, h_pre_edges⟩ := h_pre
  obtain ⟨h_g_lt, h_g_unmatched⟩ := h_guard
  subst h_trans_M
  subst h_trans_i
  set eu := edges (2 * i) with heu_def
  set ev := edges (2 * i + 1) with hev_def

  -- Well-formedness for the current edge — from pre.
  have h_edge_i : 0 ≤ eu ∧ eu < n ∧ 0 ≤ ev ∧ ev < n ∧ eu ≠ ev :=
    by ...

  -- KEY LEMMA: M extends to M' — matched stays matched.
  have h_extend : ∀ k, M k ≠ -1 →
      store (store M eu ev) ev eu k ≠ -1 := by
    intro k hk
    by_cases hk_ev : k = ev
    · simp [store, hk_ev]; omega   -- M'[ev] = eu ≥ 0 ≠ -1
    · by_cases hk_eu : k = eu
      · simp [store, hk_eu, hk_ev]; omega   -- M'[eu] = ev ≥ 0 ≠ -1
      · simp [store, hk_eu, hk_ev]; exact hk  -- M' k = M k

  refine ⟨by omega, by omega, ?_, ?_⟩
  -- MI(M') preserved.
  · ... -- store case-split on k = ev, k = eu, else
  -- maximal-up-to-(i+1)(M') preserved.
  · intro j ⟨hj0, hji⟩ ⟨h1, h2⟩
    by_cases hj_eq : j = i
    · -- j = i: M'[eu] = ev ≥ 0; contradicts h1 = -1.
      ...
    · -- j < i: use h_extend contrapositively.
      apply (h_tau_3 j ⟨hj0, by omega⟩)
      refine ⟨by_contra ..., by_contra ...⟩
      · exact h_extend (edges (2 * j)) hne h1
      · exact h_extend (edges (2 * j + 1)) hne h2
```

Three things make this proof non-trivial:

1.  **`maxHeartbeats 400000`** — default 200k aborts because
    the per-edge maximal atom (a ForAll over edge indices with
    array reads inside the antecedent) is heavy for Lean's
    elaborator.  We need to bump the budget explicitly.
2.  **`h_extend` lemma** — captures "M' extends M; once
    matched, always matched."  Without this lemma, the maximal-
    preservation step requires case-splitting on whether
    `edges(2j)` collides with `eu` or `ev`, which compounds
    badly.  Stating the extension monotonicity as a separate
    lemma factors the proof cleanly.
3.  **Contrapositive use of `h_extend`** — we want
    "M' satisfies maximal" but only have "M satisfies maximal
    up to i."  Direct argument needs to forward-propagate the
    matched-set; instead, we apply h_extend backwards:
    `M'[k] = -1 → M[k] = -1`, which directly negates the
    target.

### 6.2  `sc7_fallthrough_9d895f7d.solved.lean` — the post-bundle

The framework asks: at loop exit, given τ holds AND ¬g holds,
prove the user's `post`.

**Goal**: given `0 ≤ i' ≤ m`, MI(M'), maximal-up-to-i'(M'),
and `¬(i' < m)`, prove MI(M') ∧ maximal-for-all-edges(M').

**Proof** (~10 lines):

```lean
theorem sc7_fallthrough ... := by
  refine ⟨h_tau_2, ?_⟩            -- MI is just h_tau_2.
  intro j ⟨hj0, hjm⟩
  -- From h_tau_1 (i' ≤ m) and h_not_g (i' ≥ m), i' = m.
  -- So j < m = i', and h_tau_3 applies.
  exact h_tau_3 j ⟨hj0, by omega⟩
```

This is the *frame* the synthesizer needed for the spec to
match: the loop invariant says "maximal up to i"; at exit
where `i = m`, that becomes "maximal for all edges."

---

## 7.  The output — synthesized code + proof

After three synth runs (first two diagnosed missing helpers),
the third run succeeds in 864s.  The result:

```
Found 1 solution(s).

── solution #0 (score=61.5) ──
int[] synth(int[] edges, int m, int n, int[] M) {
    int i;
    i := 0;
    while (i < m)
        // [τ = (0 <= i) ∧ (i <= m)
        //      ∧ (∀k. 0 <= k < n ∧ M[k] != -1
        //              → 0 <= M[k] ∧ M[k] < n)
        //      ∧ (∀j. 0 <= j < i
        //              → ¬(M[edges[2*j]] = -1 ∧ M[edges[2*j+1]] = -1)),
        //    ϕ = m - i]
    {
        if (M[edges[2*i]] == -1 ∧ M[edges[2*i + 1]] == -1) {
            M, i := Update(Update(M, edges[2*i], edges[2*i + 1]),
                           edges[2*i + 1], edges[2*i]),
                    i + 1;
        }
        else if (¬(M[edges[2*i]] == -1 ∧ M[edges[2*i + 1]] == -1)) {
            i := i + 1;
        }
    }
    return M;
}
```

The framework also exposes:

  - **The picked τ subset**: `{0 ≤ i, i ≤ m, MI(M),
    maximal-up-to-i(M)}` — all four atoms were load-bearing.
  - **The picked ranking**: `m - i`.
  - **The picked guard**: `i < m`.

### 7.1  Source emitters

The same Solution can be emitted as compilable code in three
target languages via `synth.emit_py`, `synth.emit_c`, and
`synth.emit_rust`.  For this benchmark:

**Python** (default mode, proof annotations as comments):

```python
def synth(edges: list[int], m: int, n: int, M: list[int]) -> None:
    i = 0
    # invariant L0: ...
    # ranking   L0: m - i
    while i < m:
        if M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1:
            M[edges[2*i]], M[edges[2*i + 1]] = edges[2*i + 1], edges[2*i]
            i = i + 1
        elif not (M[edges[2*i]] == -1 and M[edges[2*i + 1]] == -1):
            i = i + 1
```

**Python with `runtime_check=True`** — lowers proof
obligations to `synth.proof_runtime` calls; the function
self-validates its invariants at every iteration.

**C** (`void synth(int *edges, int m, int n, int *M)`):

```c
void synth(int *edges, int m, int n, int *M) {
    int i = 0;
    /* invariant L0: ... */
    /* ranking   L0: m - i */
    while (i < m) {
        if (M[edges[2*i]] == -1 && M[edges[2*i + 1]] == -1) {
            int t0 = edges[2*i];
            int t1 = edges[2*i + 1];
            M[t0] = t1;
            M[t1] = t0;
            i = i + 1;
        }
        else if (!(M[edges[2*i]] == -1 && M[edges[2*i + 1]] == -1)) {
            i = i + 1;
        }
    }
}
```

**Rust** (`pub fn synth(edges: &[i64], m: i64, n: i64, M: &mut [i64])`):

```rust
pub fn synth(edges: &[i64], m: i64, n: i64, M: &mut [i64]) {
    let mut i: i64 = 0;
    while i < m {
        if M[(edges[(2*i) as usize]) as usize] == -1
            && M[(edges[(2*i + 1)) as usize]) as usize] == -1 {
            let t0: i64 = edges[(2*i) as usize];
            let t1: i64 = edges[(2*i + 1) as usize];
            M[t0 as usize] = t1;
            M[t1 as usize] = t0;
            i = i + 1;
        } else if ... { i = i + 1; }
    }
}
```

---

## 8.  The proof — what's machine-checked

The synthesizer guarantees that **every safety constraint** for
the chosen indicator assignment has a verifier-confirmed
"valid" verdict.  For this benchmark:

| Constraint | Solver | Note |
| --- | --- | --- |
| sc0 (entry)           | Lean (generic chain) | Vacuous MI from all-(-1) pre — aesop closes. |
| sc1 (post-bundle)     | **Lean (Tier-3 helper)** | `sc7_fallthrough_9d895f7d.solved.lean`. |
| sc2 (branch-0 inductive) | **Lean (Tier-3 helper)** | `sc2_fallthrough_d7bbb079.solved.lean`. |
| sc3 (coverage)        | Lean (generic chain) | Two guards are negations — closes by `omega`. |
| sc4 (branch-1 inductive) | Lean (generic chain) | M unchanged in skip case; MI/maximal preserved trivially. |
| sc5 (rank-dec branch 0) | Z3 (linear) | `m - i > m - (i+1)`. |
| sc6 (rank-dec branch 1) | Z3 (linear) | Same. |
| sc7 (ranking-lb)      | Z3 (linear) | `τ ⇒ m - i ≥ 0` from `i ≤ m`. |

**Trust scope**: the synthesizer trusts (1) Lean's tactic
chain and Tier-3 helpers as proof terms type-checked by Lean's
kernel; (2) Z3's UNSAT verdict on the negated obligation
(linear arithmetic).  No unverified obligations remain in the
soundness-default path.

---

## 9.  What it cost

  - **Three synth runs** (re-running after each helper landed).
    Total wall: ~2500s (~42 min) across the three.
  - **~90 lines of Lean** across the two helpers, written by
    hand.  Iterated in scratch first per CLAUDE.md convention.
  - **Zero framework changes.**  The sparse graph IR is plain
    `int[]` with paired subscripting.  Existing
    expression-language machinery (subscripts, arithmetic,
    Update) handles everything.
  - **One configuration knob**: `maxHeartbeats 400000` in the
    sc2 helper because the per-edge maximal atom is heavier
    than per-vertex atoms from earlier benchmarks.

---

## 10.  What this case study illustrates about the framework

  1. **Specifications drive the search.**  The user writes
     `pre`, `post`, and a *catalog of candidate values* per
     hole.  The framework picks a consistent combination via
     the PLDI'09 attribute-class reduction.

  2. **Two-tier verification.**  Z3 handles the cheap linear
     obligations; Lean handles quantified-array reasoning
     that Z3's quantifier-instantiation can't.  The dummy
     axiom flips the routing wholesale.

  3. **Tier-3 helpers are the escape hatch.**  When Lean's
     generic tactic chain can't close a load-bearing
     obligation, a human authors a `.solved.lean` at the
     signature-hash filename.  Future runs cache-consult it.

  4. **Sparse data structures don't need IR features.**
     `int[]` with paired indexing is enough for edge lists.
     The compositional IR generalized naturally — we got C1.A
     for free because B.1's `int[]` machinery was already
     compositional.

  5. **Synthesis closes 'real' graph algorithms.**  Greedy
     maximal matching is a textbook result, not an
     algorithm-by-axiom encoding.  The synthesizer constructed
     it from a specification, picked the loop invariant,
     verified preservation, and produced compilable code in
     three target languages.

  6. **What it does NOT do** — *yet*.  Greedy ≠ maximum
     matching; achieving sub-O(N+E) on the right graph
     classes (the L1.6 open question) requires augmenting-path
     machinery the IR doesn't have today.  C1.D bank.

---

## 11.  Glossary

  - **Atom**: a candidate value for a hole; a quantified
    predicate (for τ) or an expression (for guards, ranking,
    transitions).
  - **Hole**: a parameter in the template (e.g., `tau@L0`,
    `g@L0`, `s@B1.0`) the synthesizer fills in.
  - **Cube**: a partial assignment of indicator booleans;
    the unit of per-class enumeration.
  - **Indicator (`b_τ_i`)**: a Boolean variable for each atom
    in τ; the framework solves for which indicators are True.
  - **PLDI'09 attribute-class reduction**: the algorithm that
    enumerates per-constraint valid cubes upfront, then
    composes them into one global SAT.
  - **Tier-3 helper**: a hand-authored `.solved.lean` file at a
    signature-hash filename; the framework's escape hatch when
    Lean's generic tactic chain fails on a valid obligation.
  - **Sound-by-default**: the synthesizer's mode where every
    emitted solution has all obligations either Z3-decided or
    Lean-checked (no lenient promotion).  This benchmark runs
    under this mode.

---

## 12.  Where to go next in the codebase

  - **Spec**: `benchmarks/open_prbs/l16_bipartite_matching/bench_greedy_match_general.py`.
  - **IR + expand**: `synth/ir.py`, `synth/expand.py`.
  - **Constraint generation**: `synth/constraints.py`.
  - **Solver**: `synth/solver.py` (PLDI'09 reduction + Lean
    dispatch).
  - **Lean backend**: `synth/lean_backend/translate.py`,
    `synth/lean_backend/verify.py`.
  - **Tier-3 helpers**: `lean/SynthLean/Y2Corpus/l16_greedy_match_general/`.
  - **Emitters**: `synth/emit_c.py`, `synth/emit_py.py`,
    `synth/emit_rust.py`.

For a long-form treatment of the project: `README.md`,
`DESIGN.md` (design), `RESEARCH.md` (forward-looking threads),
`EXPERIENCE_REPORT.md` (case studies on the dev partnership).
