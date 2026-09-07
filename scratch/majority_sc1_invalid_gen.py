"""majority_sc1_invalid_gen.py — generate the 8 .invalid.lean
companions for majority_element sc1 (coverage) τ-subsets that
genuinely lack `cnt ≥ 0`.

Each .invalid.lean proves: ∃ vars, h_pre ∧ h_tau_* ∧ h_g_loop ∧
¬ (cnt = 0 ∨ cnt > 0).  The witness is the same across all 8
files (varying only in which τ atoms are bound):

  n = 1, i = 0, cnt = -1, candidate = 0, A = (fun _ => 0).

This witness satisfies:
  - n ≥ 1 ✓
  - ∃ v. count_eq A 1 v > 0:  use v = 0; count_eq A 1 0 = 1 > 0
    (via user_axiom_1 + user_axiom_0).
  - 0 ≤ i (atom 0) ✓.
  - i ≤ n (atom 1) ✓.
  - bm_inv (atom 3): ∀ v. cnt + count_eq A i candidate ≥
    count_eq A i v.  With i = 0: count_eq A 0 _ = 0 (axiom 0).
    So LHS = -1 + 0 = -1, RHS = 0.  Wait — that gives -1 ≥ 0,
    which is FALSE.
    Hmm — for bm_inv to hold at i=0, we need cnt + 0 ≥ 0, i.e.,
    cnt ≥ 0.  With cnt = -1, bm_inv DOES NOT HOLD.

  So our witness can't have bm_inv in the τ subset.  Need a
  different witness for those.

Looking at the 8 files:
  - 28170301: {0_le_i}                                       (no bm_inv)
  - 55389c8b: {0_le_i, i_le_n, bm_inv}                       (bm_inv!)
  - 6c88bc27: {i_le_n, bm_inv}                               (bm_inv!)
  - 9219e4b3: {bm_inv}                                       (bm_inv!)
  - c3326a8c: {0_le_i, i_le_n}                               (no bm_inv)
  - d59e7b31: {0_le_i, bm_inv}                               (bm_inv!)
  - e105abe6: {i_le_n}                                       (no bm_inv)
  - f56d21fe: {}                                             (no bm_inv)

For subsets WITH bm_inv, the witness cnt = -1 doesn't satisfy
the invariant.  Need a different witness: one where cnt + count_eq
is negative but ≥ count_eq.  Easiest: cnt = -1, i ≠ 0 — but i
needs to be ≥ 0 for axiom user_axiom_1 to fire.

Actually simpler approach: pick cnt = -1, i = 1 (positive).
Then bm_inv becomes ∀ v. -1 + count_eq A 1 candidate ≥
count_eq A 1 v.  With A = const 0, count_eq A 1 v = (if v = 0
then 1 else 0).  RHS for v = 0: 1.  For v ≠ 0: 0.  Need -1 +
count_eq A 1 candidate ≥ both.

If candidate = 0: count_eq A 1 0 = 1.  LHS = -1 + 1 = 0.  ≥ 1?
NO.  So bm_inv FAILS for v = 0 in this witness.

So even with cnt = -1, i = 1, candidate = 0, bm_inv fails.

We need a witness where bm_inv HOLDS but cnt ≤ -1.  bm_inv says
cnt + count_eq A i candidate ≥ count_eq A i v ∀ v.  Taking v =
candidate: cnt + count_eq A i candidate ≥ count_eq A i candidate,
i.e., cnt ≥ 0.  Contradiction with cnt = -1.

So bm_inv + cnt ≤ -1 is INFEASIBLE.  Which means:
  - subsets INCLUDING bm_inv are NOT genuinely invalid via
    cnt = -1 — they're invalid for a different reason.
    Specifically, bm_inv + h_g_loop don't entail cnt ≥ 0
    because bm_inv ALREADY entails cnt ≥ 0 (taking v = candidate)!

So the subsets with bm_inv DO transitively entail cnt ≥ 0.
Then the coverage proof SHOULD go through with bm_inv alone.
But the tactic chain failed.

This means the tactic chain has a gap, NOT that the subset is
genuinely invalid.  These should be `.solved.lean` not
`.invalid.lean`.

Conclusion: only subsets WITHOUT bm_inv (and without cnt_ge_0)
are genuinely invalid.  That's 4 of the 8:
  - 28170301: {0_le_i}
  - c3326a8c: {0_le_i, i_le_n}
  - e105abe6: {i_le_n}
  - f56d21fe: {}

The other 4 are TACTIC-CHAIN GAPS — not invalid.  Curating
them as .invalid would be incorrect.  They need .solved.lean
proofs (e.g., apply bm_inv to v = candidate to derive cnt + cnt
≥ cnt, simplify to cnt ≥ 0, then split on cnt = 0 vs > 0).

This script generates the 4 .invalid.lean files.  The other 4
need .solved.lean curation (deferred).
"""

INVALID_HASHES = {
    "28170301": "{0_le_i}",
    "c3326a8c": "{0_le_i, i_le_n}",
    "e105abe6": "{i_le_n}",
    "f56d21fe": "{}",
}

# Each .invalid.lean ships these hypotheses (subset of full τ@L0,
# none containing bm_inv).
HYP_LISTS = {
    "28170301": [("h_tau_0", "(0 ≤ i)")],
    "c3326a8c": [("h_tau_0", "(0 ≤ i)"), ("h_tau_1", "(i ≤ n)")],
    "e105abe6": [("h_tau_0", "(i ≤ n)")],
    "f56d21fe": [],
}


_PREAMBLE = """/-
Companion to `sc1_fallthrough_{hash}.failed.lean`.

VERDICT: genuinely INVALID — coverage proof `cnt = 0 ∨ cnt > 0`
requires `cnt ≥ 0` (τ atom 2) in scope.  Without it (and without
bm_inv which transitively implies cnt ≥ 0 via v = candidate), the
counterexample cnt = -1 satisfies all hypotheses but falsifies
the goal.

Counterexample: n = 1, i = 0, cnt = -1, candidate = 0,
A = (fun _ => 0).
  - Pre: n = 1 ≥ 1 ✓; ∃v. count_eq A 1 v > 0 (use v = 0,
    count_eq A 1 0 = 1 via user_axiom_1 + user_axiom_0).
  - τ subset = {hyp_set}.
  - h_g_loop: i < n is 0 < 1 ✓.
  - ¬ goal: cnt = -1, so neither cnt = 0 nor cnt > 0.

The synthesizer correctly rejects this subset under sound mode.
-/
import SynthLean.Basic
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

namespace SynthLean.VerifyTmp

theorem sc1_fallthrough_{hash}_is_invalid :
    ∃ (n candidate i cnt : Int) (A : Int → Int),
      ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))){tau_clauses_conj} ∧
      ((i < n)) ∧ ¬ (((cnt = 0)) ∨ ((cnt > 0))) := by
  refine ⟨1, 0, 0, -1, (fun _ => 0), ?_, {hyp_proofs_inline} ?_, ?_⟩
  · -- n ≥ 1 ∧ ∃ v. count_eq A n v > 0
    refine ⟨le_refl 1, 0, ?_⟩
    -- count_eq (const 0) 1 0 > 1 / 2 = 0
    have h1 : count_eq (fun (_ : Int) => (0 : Int)) 1 0
            = (count_eq (fun (_ : Int) => (0 : Int)) 0 0
               + (if ((fun (_ : Int) => (0 : Int)) 0 = 0) then 1 else 0)) := by
      have := user_axiom_1 (fun (_ : Int) => (0 : Int)) 0 0 (le_refl 0)
      simpa using this
    rw [h1, user_axiom_0]
    simp
{tau_proofs}
  · -- i < n: 0 < 1
    decide
  · -- ¬ (cnt = 0 ∨ cnt > 0): cnt = -1
    intro h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

end SynthLean.VerifyTmp
"""


def gen(hash_id: str, hyp_set: str) -> str:
    hyps = HYP_LISTS[hash_id]
    if hyps:
        tau_clauses_conj = " ∧ " + " ∧ ".join(
            f"({h[1]})" for h in hyps
        )
        tau_proofs = "\n".join(
            f"  · -- {h[0]}: {h[1]}\n    decide" for h in hyps
        )
        hyp_proofs_inline = "?_ , " * len(hyps)
    else:
        tau_clauses_conj = ""
        tau_proofs = ""
        hyp_proofs_inline = ""

    return _PREAMBLE.format(
        hash=hash_id,
        hyp_set=hyp_set,
        tau_clauses_conj=tau_clauses_conj,
        tau_proofs=tau_proofs,
        hyp_proofs_inline=hyp_proofs_inline,
    )


if __name__ == "__main__":
    import pathlib
    base = pathlib.Path(__file__).parent.parent / "lean/SynthLean/Y2Corpus/majority_element"
    for h, hyp_set in INVALID_HASHES.items():
        out_path = base / f"sc1_fallthrough_{h}.invalid.lean"
        out_path.write_text(gen(h, hyp_set))
        print(f"wrote {out_path}")
