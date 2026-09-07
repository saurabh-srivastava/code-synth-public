# Paper summaries + key insights

Foundational reference for the project.  Distills the
POPL'10 + PLDI'11 papers that the synthesizer reimplements
plus the PLDI'09 paper whose template-over-predicate-
abstraction reduction is the algorithmic backbone.

Originally `DESIGN.md §10`; moved here 2026-06-07 as part of
the doc reconcile.

---

## 10. Learnings — paper summaries + key insights

### 10.1 POPL'10 — *From Program Verification to Program Synthesis*

**Headline.** Synthesis = generalized verification. A verifier infers
invariants given known statements; leave the statements *also* unknown
and the same verifier infers code + invariants + ranking together.

**Inputs (scaffold).** `⟨F, D, R⟩`:
- `F = (Fpre, Fpost)`: functional spec.
- `D = (Dexp, Dgrd)`: expression and guard domains.
- `R = (Rflow, Rstack, Rcomp)`: flowgraph template + stack budget + op
  caps.

A separate, typically richer proof domain `Dprf` is where invariants
and ranking functions live. For our project, `Dprf` is *predicate
abstraction* — a user‑supplied atom set plus invariant templates with
conjunctive holes.

**Flowgraph grammar.** `T ::= ◦ | *(T) | T;T` plus `~` for recursion.
Conditionals fall out of acyclic blocks expanding to ≥ 2 guarded
transitions; no separate `if` non‑terminal.

**Transition‑system trick.** Acyclic code is represented as a *set*
`{ []g_i → s_i }` where each `s_i` is a conjunction of equalities
`x_j' = e_j`. Removing sequential order between assignments turns each
`s_i` into a pure fact, on equal footing with invariants and
pre/postconditions. Decoding to parallel assignment via temporaries is a
mechanical post‑step.

**Synthesis condition.** `sc = SafetyCond ∧ WellFormCond ∧ RankCond`,
of shape `∃U ∀V . sc`.

- **Safety** — `PathC` recursion: one Hoare implication per simple
  path between two invariants / program boundaries.
- **Well‑formedness** — `valid(s_i)` (each output variable assigned
  exactly once) and `⋁_i g_i` (guards tautological). *Critical*: not a
  filter, a constraint. Without it, `g_i = false ∧ s_i = false`
  trivially satisfies everything.
- **Progress** — per loop, a tracker variable `r_l = ϕ_l` (proof
  variable, never written by the body), `τ ⇒ r_l ≥ 0`, and `r_l > ϕ_l`
  after the body.

**Solver requirements.** Synthesis conditions carry **multiple positive
and multiple negative unknowns** in the same implication — vanilla
forward / backward fixed‑point tools handle one of each direction.
POPL'10 uses the PLDI'09 reduction to SAT.

**Decoding.** `Exe_π`: pick a `g_i` branch, expand `s_i` to parallel
assignment, attach `τ, ϕ` as loop annotations.

**Benchmark results.** Arithmetic (Strassen, IntSqrt three ways,
Bresenham, swap without temp), sorts (Bubble / Insertion / Selection /
Merge / Quick), DP (Fib, Checkerboard, LCS, SSSP, APSP, MatrixChain).
Median synthesis time 14 s, slowdown over verification 1×–92×.

**Honest limitations.** (a) Underlying verifier's incompleteness — no
native non‑linear arithmetic, no automatic predicate selection. (b)
Two benchmarks needed user `assume()`s. (c) Sorts/DP needed 12–20
hand‑specified predicates plus quantifier templates. (d) DPs needed
definitional axioms (e.g. Fib recurrence) passed to Z3 as quantified
asserts.

### 10.2 PLDI'11 — *Path‑based Inductive Synthesis* (PINS)

**Headline.** When loop invariants for full functional correctness are
unrealistic (compressors, encoders), drop that requirement and
symbolically execute the template instead. Each iteration picks one
path, generates a `safepath` constraint, accumulates, re‑solves. Stop
when the solution set stabilizes. Trades completeness for tractability
on programs that POPL'10 can't reach.

**Template.** `(P, Πe, Πp)` with `Πe, Πp` finite explicit sets. Holes
are pure (`ε`, `ρ`) — they evaluate without side effects, so symbolic
execution carries them through unchanged, paired with the version map
at each use site.

**Algorithm sketch.**
```
Φ := ∅;  C := terminate(P)
loop:
  sols := solve(C, Πp, Πe, m)
  if sols = ∅:    return "No Solution"   (refine template)
  if stabilized:  return sols
  S := pickOne(sols)                     -- prefer solutions contradicting many prior paths
  ⟨φ; V'⟩ := sym_exec(P, S, Φ)           -- explore one new path under S
  Φ := Φ ∪ {φ}
  C := C ∧ safepath(φ, V', spec)
```

`safepath(φ, V', spec) := ∀X . φ ⇒ spec[V']`. `terminate(P)` adds
ranking‑function constraints per loop (`bounded` and `decrease`);
inductive invariants are usually `true` and only added when needed.

**pickOne heuristic.** Pick `S ∈ sols` that contradicts (makes
antecedent false on) the largest number of paths in `Φ`. Bad solutions
survive earlier rounds by making `safepath` vacuously true on the
explored paths; the next symbolic execution under a surviving bad `S`
walks a path that exposes it. Random picking is ~20% slower.

**Termination.** Empirical, not formal: stop when sols size = previous
sols size and ≤ m. Validate with manual inspection, concrete test cases
derived from path conditions, and bounded model checking. PINS does
not guarantee correctness — it shrinks the search space and asks the
user (or downstream verifier) to spot‑check.

**Axioms.** First‑class. 8/14 benchmarks use library functions modeled
as uninterpreted symbols with quantified axioms (`strlen`, `append`,
`cos`, `sin`, `mul`/`div`).

**Template mining.** Automatic projection of the original program's
expressions/predicates yields candidate `Πe`/`Πp`; user prunes. Failure
modes are informative — a path that eliminates all candidates points at
a missing atom.

**Benchmarks.** 14 programs, 5–25 LoC. Run‑length, LZ77, LZW, Base64,
UUEncode, packet wrapper, serializer, Σi, vector shift/scale/rotate,
Dijkstra permute count, LU decomposition. Search‑space reductions of
2²⁰–2³⁷ → 1–4 candidates; times 1 s – 30 min.

### 10.3 Key insights (transferable to the new build)

1. **Verification subsumes synthesis.** Don't build a separate
   synthesis engine — build a verifier that takes some of its inputs
   (statements, guards) as unknowns drawn from a lattice. POPL'10's
   contribution and the empirical reason synthesis is tractable at all.

2. **Transition systems > sequenced statements for unknowns.** A set of
   guarded equalities erases the false ordering search; decoding to
   parallel assignment at the end is a five‑line rewrite.

3. **Well‑formedness is a constraint, not a filter.** `⋁ g_i = true`
   and one assignment per declared output variable must be asserted up
   front. Post‑hoc filtering of trash solutions doesn't scale.

4. **Tracker variables for ranking.** "ϕ decreases" with unknown ϕ has
   no clean SMT encoding; introduce `r := ϕ` at the loop head, ban
   writes to `r` in the body, and the decrease becomes an ordinary
   inequality.

5. **Templates ≠ sketches.** A sketch (Solar‑Lezama) has integer holes
   and finitized loops. A template (POPL'10) has lattice‑valued holes
   over a predicate domain — that lattice structure is what lets us
   handle unbounded loops without unrolling.

6. **`∃U ∀V` is the shape that makes synthesis hard.** Z3 handles `∀V`
   alone (E‑matching) and Boolean unknowns alone (SAT). The
   alternation is what requires the PLDI'09 reduction. Plan engineering
   effort here.

7. **Proof and program co‑constrain each other.** A statement with no
   consistent invariant is eliminated; an invariant with no consistent
   statement is eliminated. Solving for both together prunes the search
   faster than either alone — POPL'10's empirical conclusion.

8. **Small‑path‑bound hypothesis is real but partial.** PINS works
   because programs' behavior is summarized by a small carefully chosen
   path set. But "carefully chosen" matters — random path selection
   doesn't converge. `pickOne` is doing real work.

9. **Soundness vs. relative completeness vs. small‑path coverage.**
   POPL'10 has full soundness + completeness under bounds. PINS has
   path coverage only and asks the user to validate. Different tools
   for different program shapes; build POPL'10 first.

10. **A compiler framework buys two things.** (a) Free IR walks during
    constraint generation — exactly the "code walk" the user asked
    for; (b) native lowering of the synthesized output to machine
    code. MLIR wins on both criteria; LLVM IR is too low‑level;
    libclang only wins (a) and forces a C surface.

11. **The hard part of "user‑friendly synthesis" is `Πp`.** Pragna's
    biggest user friction was choosing the predicate set. The LLM will
    paper over that — but the synthesizer should still degrade
    informatively so an LLM (or human) can iterate on its guess.
    PINS's "failing paths as witnesses" pattern is the right interface;
    build it early.

12. **Axiom reuse is real.** PINS had the same string / list / arithmetic
    axioms across many benchmarks. Ship a standard library, not
    per‑benchmark copies.
