# Slice 2.B status — max-matching with axiomatized Berge — **CLOSED**

**Branch**: `c1d/slice-2b-max-matching`
**Date**: 2026-05-25
**Final synth**: v16 — 102s wall, 1 verified solution

## Final fix summary

Three changes closed Slice 2.B end-to-end:

1. **Framework**: `synth/constraints.py` `chain_paths_local`
   snapshot+restore of τ refs across Cartesian-path
   iterations.  Committed to `fix/chain-bundle-atom-refs`.

2. **Solver routing**: `synth/solver.py` allow `coverage`
   constraints with `loop_id=None` (procedure-level
   SB(n>1) coverage) to dispatch through Lean.  Previously
   gated out.

3. **Bench-level helper**: `mm_sc15_coverage` relaxed to
   require ONLY `τ@L0` atom 2 (`found ∈ {0,1}`) — proof
   uses `exact h_tau_2.symm`.  Per-subset enumeration now
   fires the helper on all τ subsets containing atom 2,
   eliminating the 8 sound-mode rejections.

The synthesized algorithm: 3-nested AP search + flip on
found, tail-recur on `M := synth(G, n, M, k - 1)`.
See bench_max_matching_recur.py.

## What's built

  - **Benchmark** (`bench_max_matching_recur.py`): tail-recursive
    AP search + flip with `phi@PROC = n - 2 * MatchingSize(M, n)`.
    Pre: `IsMatching(G, n, M)`.  Post: `IsMaxMatching(G, n, M)`.
  - **4 UFs**: `MatchingSize`, `IsMatching`, `IsMaxMatching`,
    `ExistsAugPath`.
  - **6 axioms**: matching theory + Berge + class-restriction
    (`mm_termination_implies_no_ap`).
  - **9 Tier-3 helpers** in
    `lean/SynthLean/Y2Corpus/l16_max_matching_recur/Helpers.lean`
    — all compile, all close individually via
    `verify_class_via_lean(via_helper=True)`.
  - **Framework gaps fixed** along the way:
      - `_auto_triggers` skips nested `QuantifierRef` (no
        Z3 application assertion).
      - `theorem_for_coverage` handles `loop_id=None`
        (procedure-level SB(n>1) coverage).  Walks the
        template to find the SB + accumulates τ atoms from
        preceding top-level Loops.
      - `_extract_loop_id` doesn't fall back to atom_refs
        for `coverage` kind (was mis-routing to the
        enclosing Loop).

## What's NOT yet end-to-end — framework limit found

**The synth UNSATs** instead of producing a verified solution.
Initial diagnosis was "needs an axiom for sc16."  Deeper
diagnosis revealed: **the constraint body itself is
tautologically false** under the framework's design.  No axiom
or helper can close it.

### The framework limit (root cause)

The per-procedure ranking-decrease constraint shape is:

```
path ∧ branch_guard ∧ b_recur ∧ Fpre(args)
  ⇒ phi(in_b) > phi(args_evaluated)
```

where `args_evaluated` is constructed by evaluating each
args-spec expression in the `in_b` binding context.

For our benchmark, `args = {G: G, n: n, M: M}` (identity).
Each RHS is parsed against in_b, so `args_evaluated.M = in_b.M`,
`args_evaluated.n = in_b.n`, etc.

phi = `n - 2 * MatchingSize(M, n)` evaluates to the SAME value
on both sides.  The actual generated constraint conclusion is:

```
n_state_1 - 2*MatchingSize(M_state_1, n_state_1)  >
n_state_1 - 2*MatchingSize(M_state_1, n_state_1)
```

— literally `x > x`, false for every x.

### Why the design fits rec_zero_array but not max-matching

The existing recur benchmarks pass args that are explicitly
smaller (e.g., `args.n = n - 1` in rec_zero_array).  Tail
recursion that passes IDENTITY args (our case, where the M
to recur on IS the current state's M) doesn't fit this
design.  The framework has no way to compare in_b's M against
the procedure-entry M (because it doesn't track the
procedure-entry binding separately).

## What's needed to close (refactor required)

**Option (a) — explicit iteration budget `k`**:

```python
inputs = [..., Var("k", "int", "input")]
pre = "... and k >= 0"
atoms["s@B4.0"] = [{
    "_recur": True,
    "args": {"G": "G", "n": "n", "M": "M", "k": "k - 1"},
    "ret": {"M": "M"},
}]
atoms["phi@PROC"] = ["k"]
# Guard for the recur branch asserts k > 0, so args.k = k-1 ≥ 0
# satisfies Fpre.  (Alternatively, vacuous-Fpre trick from
# lesson #18 — at k=0, args.k = -1 violates Fpre, so the IH
# is vacuous and no decrease obligation.)
```

phi(in_b) = `in_b.k`, phi(args) = `in_b.k - 1`.  Decrease
holds trivially.

User-facing API now requires `k`, an iteration budget bounded
by `n / 2` (the max number of AP-flips needed).  Caller passes
`k = n` as a safe upper bound.

**Option (b) — framework rework**: track procedure-entry-state
binding distinctly from in_b, so phi can compare across the
loop's modification of M.  Multi-day effort, touches
constraint generator's state binding model.

Estimated effort:
  - **(a)**: 2-3 hours.  Refactor benchmark (add `k` input),
    regenerate 9 helpers (new `k` binder in each signature),
    smoke-test, re-run synth.
  - **(b)**: multi-day.

Either option closes the loop end-to-end.

## What's been achieved as research

  - **Architecture validated**: 4-loop / 4 UF / 6 axiom
    benchmark generates 17 constraints; 9 of them have
    matched Tier-3 helpers that compile + verify.
  - **Framework readiness for matching theory + Berge**: the
    procedure-level multi-branch coverage gap is closed.
  - **Soundness preserved**: the synth's UNSAT is the
    correct outcome given the framework can't yet prove the
    recur decrease.  No unsound code emitted.

## Helpers manifest

| Constraint | Helper | Lines |
| --- | --- | --- |
| sc2 (L1 entry-bundle) | `mm_sc2_l1_entry` | ~30 |
| sc3 (L2 entry-bundle) | `mm_sc3_l2_entry` | ~33 |
| sc5 (L2 break + flip) | `mm_sc5_l2_break` | ~30 (cites flip-preserves-IsMatching) |
| sc6 (L2 inductive step) | `mm_sc6_l2_safety_step` | ~22 |
| sc9 (L1 body inductive) | `mm_sc9_l1_body_ind` | ~30 |
| sc11 (L0 body inductive) | `mm_sc11_l0_body_ind` | ~28 |
| sc14 (L0 final / Berge) | `mm_sc14_final_berge` | ~22 (cites class-axiom + Berge) |
| sc15 (final SB coverage) | `mm_sc15_coverage` | ~14 |

## Pickup instructions

### k-budget refactor (Option A from above) — DONE

`k` added as procedure input.  Helpers regenerated with
`k_sX` binders.  `h_pre` destructure updated to 4 conjuncts.
Synth no longer wedges on sc16; the ranking-proc-decrease
body is now `k > k - 1` (trivially true).

### Remaining issue — sc13/sc14 chain-path conflict

After the k-refactor, synth still UNSATs at 95s.  Per-
constraint diagnostic (`z3.Solver().check()` with full τ on
each constraint's body):

  - sc0-sc12, sc15, sc16: **unsat** (= body valid).
  - **sc13, sc14: unknown** under Z3.

sc13 and sc14 are BOTH `safety-bundle-post L0 branch=None`
— two Cartesian chain paths through the final SB(n=2)
(recur vs identity branches).

### Framework bug — atom_refs lost on Cartesian chain paths (FIXED 2026-05-25)

The hypothesis above turned out to be wrong.  Root cause
is in `synth/constraints.py:chain_paths_local`.

The generator calls `tau_at(...)` ONCE during `per_item`
construction (appending τ atom_refs to the shared
`current_refs`).  Then yields N Cartesian paths.  The FIRST
commit captures the refs AND clears `current_refs` (line
285).  Subsequent paths' commits get an empty
`current_refs` — so they're recorded with `atom_refs=[]`.

Effect on sc14 specifically:
  - sc13 (first Cartesian path through final SB(n=2)):
    `atom_refs` has 4 τ@L0 refs.
    `_extract_loop_id(sc13)` returns "L0".
    Helper short-circuit gating passes → helper fires.
  - sc14 (second Cartesian path):
    `atom_refs` is empty (cleared by sc13's commit).
    `_extract_loop_id(sc14)` falls back to atom_refs, gets
    nothing, returns None.
    Helper short-circuit gating fails → SKIP.

**Fix**: snapshot the refs accumulated during per_item
construction and restore them per yielded iteration so
each commit captures the same refs (`synth/constraints.py`
~line 360-415).  Trivial patch.

**Result with fix** (v11, 117.7s — vs v9's 445s + wedge):
  - **No wedge abandonments** — sc14 helper short-circuit
    now fires.
  - **Helper coverage 8/21 (38.1%)** vs v9's 6/139 (4.3%).
  - **Lean fallthrough: 18 valid / 3 unknown / 0 error**.
  - Still UNSAT but different reason — **11 Z3-side
    UNKNOWN attribute-class checks** rejected under sound
    mode, leaving some constraint without compatible cubes.

### Next remaining issue — 11 UNKNOWN attribute classes identified

After the chain-bundle atom_refs fix, the remaining UNSAT
is caused by 11 UNKNOWN attribute-class checks (rejected
under sound mode):

  - **3 ranking-lb UNKNOWNs**: sc8 (L2 ranking-lb), sc10
    (L1 ranking-lb), sc12 (L0 ranking-lb).  Z3 returns
    UNKNOWN on the hardest free-τ case (ANT-only τ, so
    empty subset = `Pre ⇒ ϕ ≥ 0`).  Routes to `_on_unknown`
    → Lean → also UNKNOWN.  Pre contains
    `IsMatching(G, n, M) == 1` (UF axiom-interactions) that
    confuse both solvers.

  - **8 coverage UNKNOWNs**: sc15 procedure-level coverage
    for the final SB(n=2): `Pre ∧ τ@L0 ∧ ¬g@L0 ⇒ g@B4.0 ∨
    g@B4.1`.  The helper `mm_sc15_coverage` covers the FULL
    τ@L0 subset.  Enumeration tries 2^3 = 8 partial subsets
    (those lacking atom 3 `IsMatching(G, n, M') == 1`),
    each goes to Lean's generic tactic chain which UNKNOWNs.

`potentially_unsound = True` does NOT help — the lenient
fallback path was excised from solver.py (line 1240-1248).

Workaround paths (in order of recommendation):
  (a) **Author per-shape helpers for ranking-lb** that
      sidestep the UF/axiom interaction.  Each one closes
      via omega/linarith since ϕ = `n - 1 - u` is linear.
      Effort: 1-2 hours per helper × 3.
  (b) **Re-introduce a gated lenient fallback** for
      `potentially_unsound = True` (was previously
      excised; would re-add ~30 LOC with a clear gate).
      Less principled but unblocks any axiom-heavy
      benchmark with sound-mode UNKNOWNs.
  (c) **Add a second sc15 helper** that proves coverage
      from a subset including just atom 2 (`found ∈ {0,1}`).
      The RHS `g@B4.0 ∨ g@B4.1 = (found==1) ∨ (found==0)`
      is trivially derivable from atom 2 alone.  This
      adds the partial-subset cubes that the synth needs
      for compositional SAT.

Estimated effort for full close: 3-5 hours (option (c) is
the principled path).
