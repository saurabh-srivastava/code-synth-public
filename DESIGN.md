# Synthesizer — Design

A proof‑theoretic program synthesizer that consumes (a) a control‑flow
template and (b) a predicate space, and produces (a) executable code and
(b) a machine‑checkable proof of partial correctness + termination. The
algorithm comes from POPL'10 ("From Program Verification to Program
Synthesis") with PLDI'11 (PINS) as a later add‑on. Implemented in
Python with Z3 + Lean 4 as dual verification backends; native codegen
(C, Python, Rust; optional MLIR/LLVM) layers on top.

Eventual flow:

```
natural language ─[LLM]→ (template, predicate space) ─[this synthesizer]→ code + proof
```

This document covers everything after the LLM and before the proof.
The LLM / NL front‑end is layered on top once the synthesizer is
robust; see [`NL_FRONTEND.md`](./NL_FRONTEND.md) for the parked plan
and `RESEARCH.md §A` for the conceptual framing.

> **Scope and currency note (2026-06-07).** This document was
> originally written at project start (2026-05-11) as the design
> plan for an unstarted implementation, then accumulated retrospective
> annotations through Phase L1.6.  In the 2026-06-07 doc reconcile,
> the §0 north stars, §8 phase log, §9 resolutions log, and
> §10 paper summaries were extracted to other docs (see pointers
> below).  Sections §2 (Inputs/outputs) and §4.2 (semantic layer)
> were rewritten to reflect the **current API** (`atoms: dict`
> with structured hole names, not the original
> `proof / guards / expressions` triple).
>
> **What's in this doc**: the design as currently
> implemented for the original capabilities — the algorithm
> (PathC, well-formedness, ranking), the ∃U∀V → SAT reduction,
> the decoding pipeline, the original list of hurdles with
> resolution notes.
>
> **What's NOT in this doc** (lives elsewhere): the **Lean
> proof backend** ([`RESEARCH.LEAN.md`](./RESEARCH.LEAN.md) +
> [`SOUNDNESS.md`](./SOUNDNESS.md)), **Tier-3 helper-citation
> codegen** ([`problem.skill`](./problem.skill) §H.2 +
> `synth/lean_backend/codegen.py`), **cost-invariant
> constraints** ([`COST_INVS.md`](./COST_INVS.md)), the
> **break primitive** ([`RESEARCH.COMPLETED.md`](./RESEARCH.COMPLETED.md)
> §K.B / §K.D), the **sound-by-default policy**
> ([`SOUNDNESS.md`](./SOUNDNESS.md)), and **chain-aware
> translators**.  Each post-Phase-3 capability has its own
> design doc.

---

## 0. Project north stars

**Moved to [`README.md`](./README.md) (2026-06-07).**
The three north stars (resource-bounded synthesis,
module-level synthesis, novel-program discovery) are
canonical in README.  The implementer-facing expansions
(NS-1 / NS-2 / NS-3) live in
[`PRINCIPLES.md`](./PRINCIPLES.md).

---

## 1. TL;DR

- **Primary algorithm: POPL'10 proof‑theoretic synthesis** over a
  *predicate‑abstraction* proof domain (à la VS3‑PA). Produces code +
  invariants + ranking functions. The LIA / bounded‑coefficient search
  path is out of scope.
- **PINS is a later add‑on**, layered on the same IR, for programs
  where full functional invariants are unrealistic (compressors,
  encoders, format converters).
- **Implementation language and codegen path:** Phase 1–4 are pure
  Python with `z3-solver`; the synthesized output is pretty‑printed
  pseudocode for inspection. C and Rust backends come **after** the
  pipeline is robust on real‑world examples (Phase 5/6). MLIR is
  *useful* but explicitly **not critical** — it slots in late as a
  unifying lowering target, only if it pays for itself by that point.
- **DSL.** Ship both forms: a Python eDSL (`SB() >> Loop(SB()) >> SB()`)
  as the canonical API, plus a small textual surface (`"SB ; LOOP { SB }
  ; SB"`) parsed into the same AST. Semantic layer (predicate space,
  axioms, spec, resource bounds) is plain Python data with a JSON
  loader on top for LLM consumption.
- **Z3 round‑trip.** We understand the encoding (POPL'10 §3,
  PLDI'09 templates‑over‑predicate‑abstraction). The risky bit is
  reimplementing the `∃U ∀V → SAT‑indicators` reduction — Z3 alone won't
  solve `∃U ∀V` directly. We re‑derive the reduction straight from
  PLDI'09 (no speculative refinements), and phase the build:
  single‑hole → conjunctive‑hole → quantified‑template.
- **Failure modes are first‑class outputs.** Two LLM‑relevant failure
  modes that need distinct telemetry: **UNSAT** (predicate space too
  strict — return witness paths à la PINS), and **timeout** (predicate
  space too loose — return hole‑size and per‑query timing telemetry so
  the LLM can prune). See §6.2.
- **Solution ranking.** Enumerate and sort by a default heuristic:
  atom count (Occam) + a simple estimated‑cost proxy. Caller can plug
  in a custom score function later.

---

## 1.1 Decisions resolved (2026‑05‑11)

These were open questions in the first cut of this plan; the user has
since fixed them. They are no longer up for debate without an explicit
reversal.

| # | Decision |
|---|---|
| 1 | **DSL surface.** Ship both. Python eDSL is canonical; textual form is a thin parser on top. |
| 2 | **MLIR.** Downgraded. Pipeline must work robustly on real examples *first*. C / Rust as primary native codegen targets eventually; MLIR is optional and late. |
| 3 | **Predicate inference.** Hand‑authored for now. Surface UNSAT‑witness paths and timeout telemetry so the LLM outer loop can iterate. |
| 4 | **Spec format.** `pre:` / `post:` as string expressions on the `Problem` object, parsed by our small expression parser. Not embedded as `assume()`/`assert()` inside the template AST. |
| 5 | **Axiom library.** Ship a standard library (strings, arrays, recursion shapes, trig) that benchmarks `import`. |
| 6 | **PLDI'09 reduction.** Re‑derive straight from the paper. No speculative refinements. |
| 7 | **Solution ranking.** Enumerate, sort by atom count + simple performance heuristic. Caller may override later. |

---

## 2. Inputs and outputs

### 2.1 Inputs — the `Problem` object

The synthesizer consumes a single `Problem` dataclass.  Current
fields (`synth/ir.py`):

| Field | Type | Required | Purpose |
|---|---|:-:|---|
| `template`         | `Template` (eDSL term: `SB`, `Loop`, `Recur`, `>>`) | ✓ | Control-flow scaffold (POPL'10 grammar `T ::= SB \| Loop(T) \| T;T \| Recur`). |
| `inputs`           | `list[Var]`              | ✓ | Input variables: `Var(name, type, role="input")` with `type ∈ {"int", "int[]", "int[][]"}`. |
| `outputs`          | `list[Var]`              | ✓ | Output variables. |
| `locals`           | `list[Var]`              |   | Local variables introduced by the template. |
| `pre`              | `str`                    |   | Precondition expression, default `"true"`. |
| `post`             | `str`                    |   | Postcondition expression, default `"true"`. |
| `atoms`            | `dict[str, list]`        | ✓ | Candidate atoms per hole, keyed by hole name (see below). |
| `uninterpreted`    | `list[(name, arg_types, return_type)]` |   | Uninterpreted function declarations. |
| `axioms`           | `list[str]`              |   | Quantified facts (passed to Z3 + Lean as assertions). |
| `max_solutions`    | `int`                    |   | Solution-enumeration cap (default 10). |
| `solver_timeout_ms`| `int`                    |   | Per-class verifier budget (default 60s). |
| `expected_solutions`/`expected_lean_hits` | `int \| None` |   | Regression-suite assertions. |
| `dump_lean_failures_dir` | `str \| None`     |   | Where to dump `.failed.lean` artifacts for `.solved.lean` curation. |
| `helper_registry`  | `HelperRegistry \| None` |   | Tier-3 helper-citation registry (`synth/lean_backend/codegen.py`). |

**`atoms` is the predicate space.**  Keys identify the hole; values
are candidate atom lists.  Hole-naming convention (set by
`synth/expand.py`):

| Key shape | Purpose |
|---|---|
| `s@B0`, `s@B1.0`, `s@B1.1`, … | Acyclic-block transition atoms.  `s@B<id>` for SB(n=1); `s@B<id>.<branch>` for SB(n≥2).  Atom is a dict `{var: rhs_expr}` representing parallel assignment, or an SSA list of dicts. |
| `g@B1.0`, `g@B1.1`, … | Per-branch guard atoms for SB(n≥2). |
| `tau@L0`, `tau@L1`, … | Loop invariant atoms (conjunctive hole — every selected atom is conjoined). |
| `g@L0`, `g@L1`, … | Loop guard atoms (single-hot). |
| `phi@L0`, `phi@L1`, … | Loop ranking-function atoms (single-hot). |
| `phi@PROC` | Per-procedure ranking for `Recur` (Phase 3.E.2). |

Transition atoms may carry framework flags:
- `{"_recur": True, "args": {...}, "ret": {...}}` — recursive self-call (POPL'10 §5.3).
- `{"_break": True, ...}` — break out of the enclosing loop (K.D primitive).

### 2.2 Outputs

`solve(problem)` returns one of three algebraic-result types
(`synth/result.py`):

- **`SolveResult(solutions: list[Solution], ...)`** — verified
  solutions, sorted by `α·atom_count + β·cost_proxy` ranking.
  Each `Solution` has:
    - `.atoms` — chosen atom per hole.
    - `.code` — pretty-printed pseudocode with invariant /
      ranking annotations attached at each loop.
    - `.score` — ranking number.
  Native source via `emit_c`, `emit_py`, `emit_rust`.
- **`NoSolution(reason, hints, unsat_core, ...)`** — predicate
  space too narrow.  `hints` enumerate possible additions; the
  LLM outer loop reads these and proposes new atoms.
- **`Timeout(reason, budget_seconds, hole_sizes, ...)`** —
  predicate space too large.  `hole_sizes` + per-class timing
  telemetry inform the LLM where to prune.

### 2.3 Worked example (max-of-array)

A current-API single-loop benchmark:

```python
from synth import Problem, SB, Loop, Var, solve, emit_c, emit_py, emit_rust

PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=2)),
    inputs   = [Var("A", "int[]", "input"), Var("n", "int", "input")],
    outputs  = [Var("m", "int", "output")],
    locals   = [Var("i", "int", "local")],
    pre      = "n >= 1",
    post     = "ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= m))",
    atoms    = {
        # Init block: m := A[0]; i := 1
        "s@B0":   [{"m": "A[0]", "i": "1"}],
        # Loop invariant (conjunctive — every selected atom is AND'd)
        "tau@L0": ["ForAll(lambda k: Implies(0 <= k and k < i, A[k] <= m))",
                   "i <= n"],
        # Loop guard (single-hot)
        "g@L0":   ["i < n"],
        # Ranking function (single-hot)
        "phi@L0": ["n - i"],
        # Two-branch loop body: take A[i] or skip
        "g@B1.0": ["A[i] > m"], "s@B1.0": [{"m": "A[i]", "i": "i + 1"}],
        "g@B1.1": ["A[i] <= m"], "s@B1.1": [{"i": "i + 1"}],
    },
)

result = solve(PROBLEM)
match result:
    case SolveResult(_):
        print(result.best.code)                        # pseudocode + proof
        print(emit_c   (result.best, PROBLEM, fname="max_array"))
        print(emit_py  (result.best, PROBLEM, fname="max_array"))
        print(emit_rust(result.best, PROBLEM, fname="max_array"))
    case NoSolution(hints=hints):
        for h in hints: print(h)                       # what to add
    case Timeout(hole_sizes=sizes):
        for k, v in sizes.items(): print(k, v)         # what to prune
```

For LLM consumption, the same `Problem` round-trips through
JSON (`synth/parse.py`).

### 2.4 What got renamed since the original plan

The original plan (2026-05-11) carried three separate fields
`proof / guards / expressions` plus `proof_templates` and
`resources`.  Phase 1 collapsed these into a single
`atoms: dict[str, list]` keyed by structured hole name.
Rationale: hole-keyed atoms cleanly cover acyclic transitions
(`s@B*`), branch guards (`g@B*.*`), loop invariants (`tau@L*`),
loop guards (`g@L*`), and ranking (`phi@L*` / `phi@PROC`) — and
makes the predicate space self-locating per template node.
`proof_templates` (conjunctive-hole structure) became implicit
in the `tau@*` conjunctive-hole semantics.  `resources`
(stack budget, op caps) was dropped; benchmarks instead
declare locals explicitly via `locals`, and cost-bound
benchmarks layer on the `cost@<lid>` holes via `COST_INVS.md`.

---

## 3. Choice of compiler framework

### Candidates considered

| Framework | Fit (template walk + constraint gen + codegen) | Cost |
|---|---|---|
| **Python eDSL + custom IR** | Excellent for Phase 1: small AST, fast iteration, `z3-solver` is native Python, JSON round‑trips trivially. | Not a "real" compiler framework. Codegen is pretty‑print only. |
| **MLIR (custom `synth` dialect)** | Excellent for Phase 2+: pass infrastructure gives us the IR walk for free; first‑class lowering to LLVM IR; clean Python bindings via `mlir-python-bindings`. | Significant build / learn / TableGen tax. Wrong tool for early algorithm churn. |
| **LLVM IR directly** | Too low‑level. Holes have no natural home (would be encoded as undef + metadata, awkward). | — |
| **Clang AST / libclang** | Pragna used the analogous Phoenix plugin. A workable surface, but it forces the DSL to be valid C, which over‑constrains everything else. | The clean‑room rebuild explicitly doesn't want this (per user direction). |
| **Roslyn / .NET** | Closest spiritual heir to Pragna. | Output codegen would be .NET IL, not LLVM. Off the modern open‑source path. |
| **Soufflé / Rust / etc.** | Wrong primitives. | — |

### Recommendation

**Python end‑to‑end through real‑world examples; then C/Rust backends; MLIR is optional and late.**

- **Phases 1–4 — Python.** The algorithm is small (POPL'10 §3 fits on
  two printed pages; the constraint‑generation visitor is a few
  hundred lines). Pure Python + `z3-solver` is the fastest path from
  zero to "synthesizes IntSqrt", and stays fast through PINS. Output
  is pretty‑printed pseudocode for inspection and for downstream LLM
  consumption.
- **Phase 5 — C / Rust backends.** Once PINS works and we have real
  benchmarks passing end‑to‑end, add real code emitters. C first (it's
  the lowest common denominator and the closest to the IML); Rust
  second. These are *templates that emit source text* — no compiler
  framework needed.
- **Phase 6 — MLIR (optional, not committed).** If by then we want a
  unified lowering target with LLVM IR codegen, define a `synth`
  dialect and let MLIR do the C → LLVM lowering. The Python algorithm
  stays put; only the codegen step moves. If we don't need it, we
  don't pay for it.

This sequencing minimises the cost of being wrong about the algorithm
(mistakes are cheap in Python), keeps the codegen decisions
independent of the synthesis logic, and defers MLIR until we have
evidence we actually want it.

### MLIR dialect sketch (Phase 6, *if and when needed*)

```
synth.func @int_sqrt(%x: i32) -> i32
    attributes { pre = "x >= 1", post = "..." } {
  synth.acyclic n=1   { Dexp=@lin, Dgrd=@lin }   // SB
  synth.loop          { Dprf=@predabs }          // *( … )
    synth.acyclic n=1 { Dexp=@lin, Dgrd=@lin }
  synth.endloop
  synth.acyclic n=1
}
```

The same template, lifted into MLIR. The constraint generator stays
Python (called via pybind); the value of the dialect is purely the
`synth.* → scf.*/arith.*/func.* → llvm` lowering path. Not justified
until benchmarks demand native execution speed; until then C source +
`clang` is enough.

---

## 4. DSL design

### 4.1 Structural layer — the flowgraph template

Faithful to POPL'10's grammar:

```
T ::= SB                 -- acyclic block ("◦")
    | Loop(T)            -- loop with body T  ("*(T)")
    | T >> T             -- sequence  (";")
    | Recur              -- recursive self‑call ("~")
```

Python eDSL (operator‑overloading on `>>` for sequence):

```python
SB() >> Loop(SB()) >> SB()                  # ◦;*(◦);◦
Loop(Loop(SB()))                            # *(*(◦))
Recur() >> Recur() >> SB()                  # ~;~;◦  (MergeSort shape)
SB() >> Recur() >> Recur()                  # ◦;~;~  (QuickSort shape)
```

Equivalent textual form (for JSON / YAML round‑trip):

```
"SB ; LOOP { SB } ; SB"
"LOOP { LOOP { SB } }"
"REC ; REC ; SB"
```

Each `SB` and `Loop` may carry attributes:

```python
SB(n=2)                                     # up to 2 guarded transitions
Loop(SB(n=2))                               # loop with a 2-branch body
```

Conditional branches fall out of `SB(n≥2)` — a multi‑transition acyclic
block expands to `choose { []g1 → s1, []g2 → s2, ... }`, and we
decode that back to `if (g1) s1 else if (g2) s2 ...` at emit time. No
separate `If` node in the grammar.

### 4.2 Semantic layer — `atoms` dict + spec + axioms

Plain Python data passed to `Problem(...)` (see the worked
example in §2.3).  JSON schema (`synth/parse.py`) is identical.
Fields:

- `atoms: dict[str, list]` — candidate atoms per hole, keyed by
  structured hole name set by `synth/expand.py`:
  - `tau@L<id>` — loop invariant atoms (conjunctive — every
    selected atom is conjoined; subset enumeration over 2^|atoms|).
  - `g@L<id>` — loop guard atoms (single-hot).
  - `phi@L<id>` — loop ranking-function atoms (single-hot).
  - `phi@PROC` — per-procedure ranking (single-hot; appears
    whenever any atom contains `_recur`).
  - `s@B<id>` — acyclic transition atom for SB(n=1).  Value is
    a dict `{var: rhs_expr}` (parallel assignment) or a list
    of single-var dicts (SSA / sequential).
  - `s@B<id>.<branch>` + `g@B<id>.<branch>` — SB(n≥2)
    per-branch transition + guard atoms.
- `pre: str` / `post: str` — pre / post-condition expressions
  (parsed by `synth/expr.py`).
- `axioms: list[str]` — quantified facts asserted to both Z3
  and Lean.
- `uninterpreted: list[(name, arg_types, return_type)]` —
  uninterpreted-function declarations.

The conjunctive-hole structure of the old design's
`proof_templates` is now implicit in the `tau@*` semantics —
every τ atom is independently selected, and the chosen subset
is conjoined.  No template literal needed.  Predicate strings
are parsed by `synth/expr.py` (not handed to Z3 directly)
because the synthesizer renames variables when generating
versioned constraints (pre vs. primed-output, per-iteration
bindings).

Transition atom values may carry framework flags:
- `{"_recur": True, "args": {...}, "ret": {...}}` — recursive
  self-call (POPL'10 §5.3; see §5.1).
- `{"_break": True, ...}` — break out of the enclosing loop
  (K.D primitive; see `RESEARCH.COMPLETED.md §K.B/§K.D`).

### 4.3 Why this DSL rather than annotated‑source

- It's lighter — no parser, no preprocessor, no preamble of macros.
- It matches the paper's mental model exactly. The grammar `T ::= ◦ |
  *(T) | T;T` *is* the template; treating it as first‑class IR is
  cleaner than embedding it in another language.
- LLM friendliness: the JSON form is structured data, no need for the
  LLM to invent valid C with subtle macro placement.
- Composability: `SB() >> Loop(...) >> SB()` is a value the user can
  build incrementally; an annotated‑source surface forces a textual
  whole‑file emit per attempt.

---

## 5. Constraint encoding — the core algorithm

Five pieces. POPL'10 §3 reproduced; in places I simplify wording for
brevity.

### 5.1 Expansion (a structured walk over the template AST)

Walk the template, generating fresh unknowns:

```
Expand(SB(n))         = choose { []g_i → s_i  :  i = 1..n }     -- g_i, s_i fresh
Expand(Loop(T))       = while_{τ,ϕ}(g) { Expand(T) }              -- τ, ϕ, g fresh
Expand(T1 >> T2)      = Expand(T1) ; Expand(T2)
Expand(Recur)         = choose { []true → s_recur }               -- POPL'10 §5.3
```

Domain constraints attach to each unknown:

- `g_i ∈ Dgrd | V`
- `s_i ∈ ⋀_j (x_j' = e_j)` with each `e_j ∈ Dexp | V`
- `τ, ϕ ∈ Dprf | V`
- `V = ~vin ∪ ~vout ∪ T ∪ L`, where `T` is local temporaries from the
  stack budget and `L` is `{iteration counter, ranking tracker}` per
  loop.

`s_recur` for recursion is `s_args ∧ (Fpre' ⇒ Fpost'') ∧ s_ret` —
the call's argument expressions are unknown, the callee is assumed
correct by induction, the returned values are placed back via another
unknown transition.

This walk is a textbook visitor. In Phase 2 it lives in an MLIR
analysis pass.

### 5.2 Safety conditions — `PathC` (POPL'10 §3.3)

Structural recursion emitting one Hoare implication per simple path:

```
PathC(φpre, choose{[]g_i→s_i}_i, φpost)
        = ⋀_i ( φpre ∧ g_i ∧ s_i  ⇒  φpost' )

PathC(φpre, while_{τ,ϕ}(g){p_l}, φpost)
        = ( φpre ⇒ τ' )
        ∧ PathC(τ ∧ g, p_l, τ)
        ∧ ( τ ∧ ¬g ⇒ φpost' )
```

Primes are output‑variable renamings (`x'` is `x` after the transition).
The three sequencing cases (loop‑then‑rest, acyclic‑then‑loop,
acyclic‑then‑loop‑then‑rest) follow POPL'10 §3.3 mechanically.

### 5.3 Well‑formedness — non‑negotiable

For every `choose{[]g_i → s_i}`:

```
WellFormTS  =  (⋀_i valid(s_i))   ∧   (⋁_i g_i)
```

- `valid(s_i)` — each output variable is assigned exactly once. In our
  DSL, the LHS variable set on a transition is *fixed* by the
  declaration of the acyclic block (we keep the list of declared output
  vars on each `SB` node), so `valid(s_i)` is structurally enforced.
  No extra constraint needed.
- `⋁_i g_i` — the guards cover the input space. The *only*
  non‑implication constraint in the whole pipeline. POPL'10 §3.4 offers
  two encodings:
  - **Direct.** Assert `⋁ g_i` as part of the synthesis condition.
    Requires a solver with multiple positive unknowns — vanilla Z3
    can't do this directly, but the predicate‑abstraction reduction
    (§5.6) flattens it to a SAT clause that Z3 can.
  - **Iterative.** Solve one `(g, s)` at a time; if `⋁ g_i` so far is
    not a tautology, assert `¬(g_{i+1} ⇒ ⋁ g_i)` and re‑solve;
    repeat to a fixed point.

Phase 1 uses the iterative encoding (works with any solver). Phase 2+
adds direct once the full reduction is in place.

*Why this matters.* Without `⋁ g_i ≡ true` and `valid(s_i)`, the
trivial assignment `g_i = false ∧ s_i = false` satisfies every
implication. Past synthesis attempts have failed by trying to filter
that garbage post‑hoc; POPL'10's contribution is that it's a constraint,
not an afterthought.

### 5.4 Progress — ranking functions

For each loop `l = while_{τ,ϕ_l}(g) { p }`:

```
prog(l)  =  (r_l = ϕ_l)                                    -- tracker (proof variable)
         ∧  (τ ⇒ r_l ≥ 0)                                  -- lower bound
         ∧  PathC(τ ∧ g, p, r_l > ϕ_l)                     -- decrease across body
```

`r_l` is declared as a *proof variable*: no body assignments touch it,
so it freezes ϕ's value at the loop head, and the decrease check
`r_l > ϕ_l` after one iteration is an ordinary inequality. (Trying to
say "the unknown ϕ_l decreases" directly has no clean SMT encoding;
the tracker is the trick.)

For nested loops: replace `p` with the suffix `end(l)` after the
innermost loop, and use that loop's invariant `τ_end` as the
precondition. This relies on the inner invariant carrying enough
information; if it doesn't, the synthesizer fails and we either
strengthen the inner invariant template or fall back to PINS's simpler
ranking encoding (Phase 4).

### 5.5 The composite synthesis condition

```
sc  =  SafetyCond(exp, F)  ∧  WellFormCond(exp)  ∧  RankCond(exp)
form: ∃ U . ∀ V . sc
```

`U` is the union of all fresh unknowns `(g_i, s_i, τ, ϕ, r)`. `V` is
the union of all program variables across all version maps.

### 5.6 Reducing `∃U ∀V` to something Z3 will actually solve

**This is the single hardest piece of code in the project.** Z3 cannot
solve `∃U ∀V` directly for arbitrary `U`. The reduction comes from
Srivastava & Gulwani PLDI'09 ("Program Verification using Templates
over Predicate Abstraction") and is the engine underneath VS3‑PA.

Restated for our setting:

1. Each unknown lives in a *finite lattice*:
   - Invariants `τ`: choose a conjunction (subset) of the proof atoms
     for each conjunctive hole in the chosen invariant template.
   - Statements `s_i`: each LHS slot picks one expression from
     `Dexp | V`.
   - Guards `g_i`: choose a conjunction (or disjunction, per template)
     of guard atoms.
2. Introduce one **Boolean indicator variable** per (hole, atom) pair.
   The total number of Boolean unknowns is `|holes| × |atoms|`,
   typically a few hundred — well inside SAT's comfort zone.
3. For each implication `Pre ⇒ Post` in `sc`, query Z3 a polynomial
   number of times to extract the *valid attribute classes* —
   combinations of atom assignments to the holes for which the
   implication holds. Encode each valid class as a Boolean clause over
   the indicators.
4. The conjunction of all clauses is a SAT instance over the
   indicators. A satisfying assignment reads back as a choice of atoms
   per hole.

The key property (POPL'10 §4.2 Property 1): the SAT instance is
satisfiable **iff** the original synthesis condition has a solution in
the chosen template space. That is the soundness‑and‑completeness
anchor.

#### Phased implementation of the reduction

- **Phase 1.A** — *Single‑hole, single‑atom*. Each unknown selects
  exactly one atom from its space. Indicators are `b_{u,k}` with the
  single‑hot constraint `⋀_u ⋁_k b_{u,k} ∧ (¬ pairs)`. The "polynomial
  Z3 queries" collapse to one query per (implication, atom‑combination).
  This is enough for IntSqrt with a tiny atom set.

- **Phase 1.B** — *Conjunctive holes over the proof domain*. The `[-]`
  hole in an invariant template picks a *subset* of atoms (conjunction).
  Indicators are still `b_{u,k}` but no single‑hot constraint. The
  attribute‑class extraction now subsets, and we re‑query Z3 per subset
  reachable by adding one atom at a time (standard
  abstract‑interpretation lattice climb).

- **Phase 1.C** — *Quantified templates*. `forall k. [-] ⇒ [-]` is the
  shape sorting and DP need. The reduction is structurally the same; the
  Z3 queries now go via E‑matching with quantified axioms.

The reference C# implementation in `ref/pins-src/Domains/QuantifiedDomain/`
(specifically `QuantifiedSAT.cs`, `VCSolve-SAT.cs`,
`BooleanProver*.cs`) is a useful cross‑check against the
re‑derivation — when our Phase 1.C output diverges from the published
benchmarks, we compare what we extract against the old code's attribute
classes.

---

## 6. Decoding the result

The synthesizer has three possible outcomes per call. Each is a
first‑class output with structure designed for the LLM outer loop to
consume.

### 6.1 SAT — decoding Z3 model → code + proof

A satisfying SAT assignment `π` over the indicators gives, per hole,
which atoms participate. Reconstruction:

```
π(g)        =  conjunction (or disjunction, per template) of selected guard atoms
π(s)        =  ⋀_j (x_j' = e_j), with each e_j chosen by single‑hot indicators
π(τ), π(ϕ)  =  template instantiation, conjunctive holes filled with
               selected proof atoms
```

Then `Exe_π` rewrites the template AST into ordinary imperative code
(POPL'10 §4):

```
Exe_π(while_{τ,ϕ}(g) { p })
    →  while (π(g)) { Exe_π(p) }    [with invariant π(τ), ranking π(ϕ)]

Exe_π(choose {[]g_i → s_i})
    →  if      (π(g_1)) { Stmt(π(s_1)) }
       else if (π(g_2)) { Stmt(π(s_2)) }
       ...

Stmt(⋀_i x_i = e_i)
    →  t_1 := e_1; … ; t_n := e_n;          -- via temporaries
       x_1 := t_1; … ; x_n := t_n;           -- (parallel assignment)
```

In Phase 1, emit pretty‑printed pseudocode. In Phase 5, C source. In
Phase 6 (optional), lower to MLIR `scf` + `arith` + `func` and attach
`synth.invariant`, `synth.ranking` as op attributes; standard
pipelines take it to LLVM IR.

#### Multiple solutions

Enumerate by repeatedly asserting `⋁ b_{u,k} ≠ π(b_{u,k})` and
re‑solving (POPL'10 §5.6; PINS §2.3 does the same). Default ranking
is `score(solution) = α * atom_count + β * estimated_cost`, with a
simple cost proxy (count of branches and loop bodies). Caller can
plug in a custom `score: Solution → float` callback to override.

### 6.2 UNSAT — "predicate space too strict"

Z3 returns `unsat`. The most likely cause is a missing predicate or
expression atom in the user's space. Output:

```
NoSolution(
  reason          = "unsat",
  witness_paths   = [...],          # per-path conditions that became unsatisfiable
  pinned_unknowns = {τ: [...], g: [...]},  # which holes had zero valid atom assignments
  unsat_core      = [c1, c3, c7],   # smallest core, via Z3 unsat-core
  hints           = [...],          # heuristic suggestions, e.g. "no atom in proof: covers ⟨relation⟩"
)
```

This is the PINS "failing paths as witnesses" pattern, formalized for
the proof‑theoretic case. The LLM outer loop can read `witness_paths`
+ `hints` and propose new atoms.

### 6.3 Timeout — "predicate space too loose / too large"

Z3 times out (or the per‑query budget overflows). The most likely
cause is too many atoms, too many conjunctive‑hole combinations, or
non‑linear blow‑up on quadratic atoms. Output:

```
Timeout(
  reason             = "timeout",
  budget_seconds     = …,
  hole_sizes         = {τ: 8 atoms, g0: 4 atoms, s1: 12 atoms},   # which space is biggest
  expensive_queries  = [(implication_id, seconds), …],            # which constraints stalled Z3
  partial_solutions  = […],                                       # any solutions found before timeout
  hints              = [...],     # heuristic, e.g. "consider dropping non-linear atom 'v == i*i' or splitting the proof template"
)
```

`hole_sizes` and `expensive_queries` are the LLM's signal for which
part of the space to prune. Without these channels, the LLM is
guessing in the dark.

#### Implementation note

The three outcomes are an algebraic type, not a single union with
`None`. The Phase 1 prototype must return `SolveResult` /
`NoSolution` / `Timeout` distinctly so downstream callers can pattern
match. This is a small interface decision but it shapes the LLM
outer loop API for years.

---

## 7. Biggest hurdles, ranked

1. **The `∃U ∀V → SAT‑indicators` reduction.** PLDI'09 algorithm.
   Single biggest engineering item. *Mitigation*: phased build —
   single‑hole, then conjunctive holes, then quantified templates.
   **RESOLVED** (Phase 3.X.2, attribute-class enumeration with
   push/pop reuse + Phase 3.L monotonicity-aware fast path; see
   CLAUDE.md).

2. **Predicate set authoring.** Pragna's biggest user‑facing friction was
   choosing `Πp`. For our flow the LLM will guess, but the synthesizer
   should fail informatively (which atoms / paths killed the search) so
   the next iteration of the guess improves. PLDI'11's "failing paths as
   witnesses" pattern is the right interface; build it from day 1.
   **PARTIALLY RESOLVED**: `NoSolution(hints, pinned_unknowns, …)` and
   `Timeout(hole_sizes, …)` are emitted; PINS-style failing-path
   witnesses are still future work (Phase 4).

3. **Quantified invariants** for sorts and DP. `forall k. 0 ≤ k < i ⇒
   A[k] ≤ A[k+1]` requires the quantified‑template path
   (Phase 1.C). The template structure is user‑supplied for now; auto
   inference is research‑grade work and explicitly deferred.
   **RESOLVED for hand-authored templates** (Phase 3.B/3.C/3.D):
   `ForAll`/`Exists` parse via Python lambdas; multi-variable
   binders work; bubble sort + Bresenham's full pixel-correctness
   post both verified.  Auto-inference still deferred.

4. **Termination for nested loops.** Outer ranking decrease relies on
   the inner invariant carrying enough info (POPL'10 §3.5). Fragile in
   practice — POPL'10 itself had to annotate three sorting benchmarks
   to skip outer invariants. *Mitigation*: support manual hints
   (`skip_invariant_at: loop_id`) and the PINS‑style "treat inner loops
   as atomically terminating" fallback.
   **RESOLVED differently** (Phase 3.K): frame equations through the
   abstract Loop transition (preserve every var NOT in the body's
   modified set).  No manual hint flag needed.  See CLAUDE.md lesson
   #19.  Bubble sort + selection sort + nested counter all verified.

5. **Axioms / uninterpreted functions.** Both papers use them
   extensively. Plumb `axioms:` and `uninterpreted:` directly to Z3
   `assert` and `declare-fun`. Reusable axiom packs (strings, arrays,
   trig) shared via a small library.
   **RESOLVED** (Phase 3.D): `Problem.uninterpreted` and
   `Problem.axioms` plumbed end-to-end; fib benchmark uses recurrence
   axioms.  Reusable packs are a TODO (no benchmark needs them yet).

6. **Z3 quantifier handling.** Even after the indicator reduction, the
   per‑implication queries are `∀V` over program variables. E‑matching
   is brittle; sometimes Z3 says `unknown`. *Mitigation*: hand‑written
   instantiation patterns where E‑matching fails; bounded‑V fallback
   (bit‑blasting) for small `V`.
   **PARTIALLY RESOLVED**: auto-trigger inference for quantified
   atoms (Phase 3.X.3) is in place; bounded-V fallback hasn't been
   needed.  `_PER_CHECK_TIMEOUT_MS` budgets the per-class Z3 query.

7. **Scaling.** POPL'10 reported up to 2.5 h on Bresenham's; PINS
   reported up to 30 min on LZ77. Slow. *Mitigation*: don't optimize
   early. Profile first. Easy wins: incremental Z3 (`push`/`pop`)
   per path; parallel exploration of independent paths; solution caching
   across enumeration rounds.
   **PARTIALLY RESOLVED**: push/pop reuse (Phase 3.X.3) and the Phase
   3.L monotonicity fast path together get Bresenham's full quantified
   post under 5s and bubble sort under 10s — well under POPL'10's
   2.5h.  Parallel exploration / cross-round caching not yet needed.

8. **The MLIR ramp.** Non‑trivial; must not block Phase 1 correctness.
   *Mitigation*: defer until Phase 2 and only after we have working
   benchmarks in pure Python.
   **DEFERRED** — Phase 6, optional.  C emitter (Phase 5.A/5.B) is
   the active codegen target.

9. **Output validation.** POPL'10 outputs come with a re‑checkable
   proof; PINS outputs do not (path coverage only). *Mitigation*: emit
   proofs in SMT‑LIB so a downstream solver can re‑validate;
   bounded‑model‑check PINS outputs separately.
   **PARTIALLY RESOLVED**: invariants + ranking functions are emitted
   as proof annotations in the synthesized code (`decode.py` /
   `emit_c.py`).  Full SMT-LIB re-export is future work.

10. **Non‑linear arithmetic in atoms.** Out of scope as a *path* (no
    LIA coefficient search), but predicates like `v == i*i` will appear
    in the atom set. *Mitigation*: hand them to Z3's NRA tactic; let
    users supply axioms when Z3 chokes. Both POPL'10 §5.1 and PLDI'11
    handled this by accepting incompleteness and letting the user add
    assumptions.
    **RESOLVED** in practice (Phase 0–3): IntSqrt (`v == i*i`), mul
    (bilinear), intdiv (bilinear), Bresenham's (bilinear in
    quantified body) all work via Z3 NRA on quantifier-free per-check
    queries.  No user-supplied non-linear axiom has been needed.

---

## 8. Phased implementation plan

**Moved to [`CHANGELOG.md`](./CHANGELOG.md) (2026-06-07).**
Phase-by-phase markers (Phase 0 through Phase L1.6 breadth)
with body, lessons banked, milestone status all live in
CHANGELOG.md.  The most recent 2-3 phases also stay inline
in [`CLAUDE.md`](./CLAUDE.md) for active-session context.

---

## 9. Resolutions log (2026‑05‑11)

**Folded into [`CHANGELOG.md`](./CHANGELOG.md) (2026-06-07).**
The seven open-question resolutions from the first cut of
this plan live in CHANGELOG.md's project-start entries.
§1.1 above retains the summary table.

---

## 10. Learnings — paper summaries + key insights

**Moved to [`ref/PAPERS.md`](./ref/PAPERS.md)
(2026-06-07).**  POPL'10 + PLDI'11 + PLDI'09 summaries and
the transferable insights derived from them live there.

---

## 11. Research directions (post‑foundations)

See **`RESEARCH.md`** for the full pitch.  Brief:

- **§A** — Natural-language front-end via a small (8B–32B) LLM,
  using `problem.skill` and `debug.skill` as in-context guides.
  The synthesizer is the trust boundary; the LLM iterates against
  structured UNSAT / Timeout failure channels.
- **§B** — Lean 4 tactic-based proof backend alongside the SMT
  path, for problems where structural induction or dependent types
  are more natural than brute-force atom enumeration.

Both are *post-foundations* — gated on Phase 5+ source emitters
working on real-world examples and the constraint-emission
centralization being battle-tested.  See `RESEARCH.md` §C for the
dependency rationale.

### 11.3 Parked: narrower Z3-suspect filter

**Moved to [`RESEARCH.md §M.PARKED`](./RESEARCH.md)
(2026-06-07).**

