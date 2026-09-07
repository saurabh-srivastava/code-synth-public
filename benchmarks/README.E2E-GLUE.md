# End-to-end glue: from per-VC proofs to `program ⊨ spec`

This note describes a small, reusable construction that closes the last gap in
a benchmark's proof trail — the step that turns *"each verification condition is
machine-checked"* into *"the synthesized program meets its specification."*

Worked reference: [`verina/verina_basic_47`](verina/verina_basic_47) — the glue
lives at
`verina/verina_basic_47/lean/SynthLean/Y2Corpus/verina_basic_47/arraySum.glue.lean`
and compiles standalone under core Lean.

---

## 1. The gap this closes

A solved benchmark ships a set of `*.solved.lean` files. Each discharges **one**
proof obligation the synthesizer generated — for a single `while` loop, the
classic Floyd/Hoare triple:

| `.solved.lean` file | Hoare role | Obligation |
| --- | --- | --- |
| `sc0_…` (entry) | **initiation** | `{Pre} init {τ}` |
| `sc1_…` (loop-inductive) | **consecution** | `{τ ∧ g} body {τ}` |
| `sc4_…` (post/exit) | **exit** | `τ ∧ ¬g ⟹ Post` |
| (Z3-side, no `.lean`) | **termination** | `τ ∧ g ⟹ φ ≥ 0`, and `φ` decreases |

These are individually valid, but **no artifact states the composed claim**

```
Pre  ⟹  the program halts  ∧  its result satisfies Post.
```

That composition — "these particular obligations, together, certify the program"
— normally lives *untyped and unchecked* in the Python VC-generator and SAT layer
(`synth/constraints.py`, `synth/solver.py`; see `SOUNDNESS.md`). The glue lifts it
into a single checked Lean theorem.

---

## 2. The construction

Two parts: a **reusable core** (write once) and a **per-benchmark instantiation**.

### 2a. Reusable core (shared by every single-loop benchmark)

A big-step model of `while g do body`, and the generic partial-correctness rule
proved by induction on the execution derivation:

```lean
inductive Exec (g : S → Prop) (body : S → S) : S → S → Prop
  | stop (s : S) (h : ¬ g s) : Exec g body s s
  | step (s s' : S) (h : g s) (rest : Exec g body (body s) s') : Exec g body s s'

theorem while_rule (pres : ∀ s, I s → g s → I (body s)) :
    ∀ {s s'}, Exec g body s s' → I s → I s' ∧ ¬ g s' := by
  intro s s' e
  induction e with
  | stop s h             => exact fun hi => ⟨hi, h⟩
  | step s s' hg rest ih => exact fun hi => ih (pres s hi hg)
```

`while_rule` **is** the composition metatheorem. Existence of an `Exec … s s'`
derivation encodes termination; `while_rule` propagates the invariant along it.

### 2b. Per-benchmark instantiation

Model the loop's state and its three atoms as Lean objects, restate the VC
content, prove termination against the ranking function, and assemble the
capstone:

```lean
structure St where result : Int; i : Int          -- the live variables
def gg : St → Prop := fun s => s.i < n            -- guard   (atoms g@L0)
def bb : St → St   := fun s => {result := s.result + A s.i, i := s.i + 1}  -- body (s@B1)
def II : St → Prop := fun s => 0 ≤ s.i ∧ s.i ≤ n ∧ s.result = sum A s.i   -- invariant (τ@L0)

theorem pres_lemma  : ∀ s, II A n s → gg n s → II A n (bb A s)  -- = sc1 content
theorem terminates  : ∀ s, ∃ s', Exec (gg n) (bb A) s s'        -- WF on φ = n − i
theorem arraySum_total (h_pre : n ≥ 1) :
    ∃ s', Exec (gg n) (bb A) {result := 0, i := 0} s' ∧ s'.result = sum A n
```

`arraySum_total` feeds the entry fact (`sc0`), `while_rule (pres_lemma …)`
(`sc1`), and the exit reasoning (`sc4`) into one proof — plus a real
`terminates`. `#print axioms` shows no `sorry`; the only domain axioms are the
`sum` recurrences (same trust surface as the `.solved.lean` files).

---

## 3. What's machine-checked vs. still trusted

The glue is a strict improvement, but be precise about what it buys:

**Newly machine-checked (was assumed before):**
- the **composition metatheorem** (`while_rule`) — previously only asserted by
  the VC-generator;
- **termination** — previously a Z3 SAT verdict outside Lean, now a well-founded
  proof.

**Still trusted — the seam MOVED, it was not removed:**
- `Exec`/`gg`/`bb`/`II` is a **hand-written Lean model** of the loop. Nothing here
  proves it faithfully represents `synthesized.py` / the synthesizer IR. The
  trusted step shrank from *"the VC-generator is sound"* (a semantic property of
  a program) to *"this Lean model transliterates the IR"* (a syntactic,
  auditable, mechanizable check). Close it fully by **generating** the model from
  the IR (see §6, tier 2).
- **Spec fidelity** is unchanged: the `sum` axioms restate VERINA's `sumTo`, and
  the final link `sumTo a a.size = a.toList.sum` (the *intent* tie) is still an
  informal argument in `problem.py`, not a proof.

---

## 4. Recipe: gluing a benchmark from its artifacts

Every slot in the glue is filled directly from artifacts the benchmark already
ships. This is the whole point — the mapping is mechanical.

| Glue slot | Source artifact | Field |
| --- | --- | --- |
| `structure St` fields | `problem.py` | `outputs` + `locals` (the vars the body mutates) |
| section `variable`s | `problem.py` | `inputs` |
| `axiom sum …` | `problem.py` | `uninterpreted` + `axioms` (also copied verbatim in each `.solved.lean`) |
| `def gg` (guard) | `problem.py` | `atoms["g@L0"]` |
| `def bb` (body) | `problem.py` | `atoms["s@B1"]` |
| `def II` (invariant) | `problem.py` / `invariants.md` | `atoms["tau@L0"]` |
| init state literal | `problem.py` | `atoms["s@B0"]` |
| `termination_by` measure | `problem.py` / `invariants.md` | `atoms["phi@L0"]` (ranking) |
| `h_pre` hypothesis | `problem.py` | `pre` |
| capstone conclusion (Post) | `problem.py` / `verina-spec.md` | `post` |
| `pres_lemma` proof body | `sc1_…solved.lean` | reuse verbatim / adapt |
| entry proof body | `sc0_…solved.lean` | reuse verbatim / adapt |
| exit proof body | `sc4_…solved.lean` | reuse verbatim / adapt |

Procedure:

1. **State.** One `structure St` field per mutated variable (`outputs ∪ locals`);
   inputs become section `variable`s.
2. **Atoms → Lean.** Transcribe `g@L0`, `s@B1`, `tau@L0` into `gg`, `bb`, `II`.
   Copy the UF axioms.
3. **Consecution.** Port `sc1`'s tactic block into `pres_lemma`
   (goal shape is identical: `II (bb s)` from `II s ∧ gg s`).
4. **Termination.** `by_cases` on the guard; recurse on `bb s`;
   `termination_by <φ>.toNat`; `decreasing_by simp only [bb]; omega`.
   Surface the guard as a plain hypothesis (`have hlt : … := hg`) so `omega`
   can read it.
5. **Capstone.** `terminates` gives the run; `while_rule (pres_lemma …)` carries
   `II` to the exit; port `sc0` for entry and `sc4` for exit; `rw` to Post.
6. **Trailing SBs.** A *no-op* trailing block (e.g. `s@B2 = {}`) vanishes — state
   the Post on the loop-exit state directly. A non-trivial trailing block needs
   one extra `bb`-style step composed after the loop.

**Check** (no build step; standalone file):

```bash
cd lean && lake env lean \
  ../benchmarks/<suite>/<task>/lean/SynthLean/Y2Corpus/<task>/<name>.glue.lean
# expect: `… depends on axioms: [propext, <UF axioms>, Classical.choice, Quot.sound]`
# a `sorryAx` in that list means a subproof is incomplete.
```

---

## 5. Scope and limits

The reusable core above covers exactly **one unnested `while`** over a state that
is a tuple of integers/total-function arrays. Each of the following needs more
one-time core work (a richer `Exec`, or an added rule) — engineering, not
research:

- **Sequenced loops** — compose two `Exec`s; thread the mid-state invariant.
- **Nested loops** — inner loop becomes the `body`; needs its own invariant/rule.
- **Branches in the body** — `body : S → S` still works if the branch is total;
  a branch that changes control flow needs the guard/rule generalized.
- **`break` / early return** — `Exec` needs an explicit terminal-reason.
- **Bounds-checked arrays** — the `A : Int → Int` model *defines away* memory
  safety; a faithful model reintroduces an array-bounds obligation.

---

## 6. Effort tiers

1. **Hand-glue one single-loop benchmark** — ~40–60 lines, ~1 hour. The reusable
   core is ~12 of those lines and is written once. *(Done for `verina_basic_47`.)*
2. **Auto-emit the glue from the IR** — the high-value move. The existing Lean
   translator already emits `sc0/sc1/sc4` from the chosen atoms; extend it to
   fill the §4 template slots and reuse the one `while_rule`. Days to ~2 weeks
   with tests. Upgrades every single-loop benchmark's headline claim from
   "N VCs checked" to "one theorem: `program ⊨ spec`."
3. **Certified VC-generator** — prove the emitter sound against an operational
   semantics of the IR, eliminating the §3 model↔IR seam entirely.
   Weeks-to-months; research-grade; only needed if a small mechanical emitter is
   not trusted.
