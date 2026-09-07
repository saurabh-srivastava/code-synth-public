# Slice 2.C status — concrete IsMatching + Tier-1 flip preservation — **CLOSED**

**Branch**: `slice-2c-concrete-matching`
**Date**: 2026-05-27
**Final synth**: v6 — 131.9s, 1 verified solution

## What's built

The structural pieces and the load-bearing Tier-1 proof are in:

1. **`bench_max_matching_concrete.py`** — Slice 2.B's bench
   forked + concretized:
   - DROPPED UFs: `MatchingSize`, `IsMatching`.
   - KEPT UFs: `IsMaxMatching`, `ExistsAugPath`.
   - Concrete IsMatching: **4 atoms** (range, symm, no_self,
     edge — `_MI_*` constants).  The `no_self` atom is new vs
     Slice 2.B and IS load-bearing — without it the
     flip-preserves-IM proof's case analysis fails because the
     predicate admits `M[v] = v`.
   - Added local `c : int` counter (incremented `c := c + 2`
     in the AP-flip branch).
   - τ@L0 → **8 atoms** (was 4); τ@L1 → **10**; τ@L2 → **12**.
   - Axioms: Berge + class-restriction rewritten to take the 4
     concrete IM atoms.

2. **`lean/.../l16_max_matching_concrete/Helpers.lean`** — all
   helpers compile under `lake build`:
   - **`flip_preserves_im` — Tier-1 PROVEN theorem** (the
     user's explicit deliverable).  ~120 LOC of real Lean
     proof: case-splits `kk ∈ {u, v, M v, w}` vs otherwise,
     uses pointwise store-unfolding + M's 4 atoms.  Replaces
     Slice 2.B's `mm_flip_preserves_matching` AXIOM.
   - **Axioms** `mm_berge`, `mm_termination_implies_no_ap`
     (user-approved to keep Berge axiomatic).
   - **8 Tier-1 helpers** `mm_sc2..mm_sc15`: rewritten to
     destructure the 4 concrete IM atoms instead of the UF.
     `mm_sc5_l2_break` cites `flip_preserves_im` directly
     (Tier-1 chain).  `mm_sc14_final_berge` cites
     `mm_termination_implies_no_ap` then `mm_berge`.

## What's NOT yet end-to-end

**Synth wedges on sc1** (safety-bundle-entry L0).  Direct
`verify_class_via_lean` on sc1 with the FULL τ@L0 subset
returns `valid` in 7s — so the obligation is provable.
But during synth, sc1 sat at "0 dispatches completed"
through 160s of monitoring (Lake processes running but not
reporting back via the executor).

Likely cause: NO helper registered for sc1 (Slice 2.B also
lacked one but had only 4 τ atoms vs Slice 2.C's 8).
Enumeration kicks in; even with Phase 3.L's monotonicity
fast-path collapsing CONS-only τ to one dispatch per
non-τ-hole combo, the Lean dispatches don't surface in the
counter.

## Workaround paths

1. **Add an sc1 helper** (safety-bundle-entry L0) — proof
   is straightforward: destructure h_pre to extract the 4 IM
   atoms, refine the conjunction with each.  ~30 LOC.

2. **Debug the executor / dispatch counter** — investigate
   why `lean_dispatch_hits/misses/errors` stay at 0 while
   Lake processes ARE running.  Possible parallelism issue
   or counter not being updated in some code path.

3. **Reduce parallel workers** to serial dispatch — eliminates
   any contention.  Per lesson #62 from the L1.6 Slice C
   work, parallel workers cause Lean cache contention on
   axiom-heavy benchmarks.  Worth trying
   `solver_parallel_workers=1` if such a knob exists.

## Branch state

5 commits on `slice-2c-concrete-matching`:
- `968f950` Slice 2.C bench: fix axiom paren balance
- `042250b` Slice 2.C: 8 helpers + flip_preserves_im as Tier-1
- `66921f4` Slice 2.C scaffold
- `7878b4e` scratch: Tier-1 proof for flip-preserves-IsMatching
- (plus shared earlier commits)

The Tier-1 deliverable (`flip_preserves_im` proven from first
principles, replacing Slice 2.B's axiom) is the load-bearing
research win.  E2E synth closure is incremental work pending
investigation of the sc1 dispatch wedge.
