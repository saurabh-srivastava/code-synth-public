"""majority_sc1_solved_gen.py — generate .solved.lean for the 4
majority sc1 (coverage) τ-subsets that contain bm_inv.

These subsets ARE provable but the generic tactic chain doesn't
close them.  The proof citing bm_inv:

  Apply h_bm_inv to v = candidate.
  Result: cnt + count_eq A i candidate ≥ count_eq A i candidate.
  Subtract: cnt ≥ 0.
  Then omega closes (cnt = 0 ∨ cnt > 0).

For each .failed.lean dump, bm_inv is at a different h_tau_N
position (because the chosen-subset's atom indices vary).  Look
up the position from the .failed.lean dump and emit the
correct citation.
"""

# Hash → (full hypothesis list with h_tau_N positions).
# h_tau_<bm_pos> is the bm_inv atom; others are 0 ≤ i / i ≤ n.
HYP_TABLE = {
    "55389c8b": {  # {0 ≤ i, i ≤ n, bm_inv} — bm_inv at h_tau_2
        "binders": [
            ("h_tau_0", "(0 ≤ i)"),
            ("h_tau_1", "(i ≤ n)"),
            ("h_tau_2",
             "(∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v)))"),
        ],
        "bm_hyp": "h_tau_2",
    },
    "6c88bc27": {  # {i ≤ n, bm_inv} — bm_inv at h_tau_1
        "binders": [
            ("h_tau_0", "(i ≤ n)"),
            ("h_tau_1",
             "(∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v)))"),
        ],
        "bm_hyp": "h_tau_1",
    },
    "9219e4b3": {  # {bm_inv} — bm_inv at h_tau_0
        "binders": [
            ("h_tau_0",
             "(∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v)))"),
        ],
        "bm_hyp": "h_tau_0",
    },
    "d59e7b31": {  # {0 ≤ i, bm_inv} — bm_inv at h_tau_1
        "binders": [
            ("h_tau_0", "(0 ≤ i)"),
            ("h_tau_1",
             "(∀ v : Int, ((cnt + (count_eq A i candidate)) ≥ (count_eq A i v)))"),
        ],
        "bm_hyp": "h_tau_1",
    },
}


_TEMPLATE = """/-
Companion to `sc1_fallthrough_{hash}.failed.lean`.

VERDICT: PROVABLE — coverage proof `cnt = 0 ∨ cnt > 0` follows
from the bm_inv hypothesis by specializing v = candidate:
  cnt + count_eq A i candidate ≥ count_eq A i candidate
⇒ cnt ≥ 0
⇒ cnt = 0 ∨ cnt > 0.

The generic tactic chain didn't discover this specialization
(omega / nlinarith don't quantifier-instantiate; aesop / decide
don't see the pattern).  Hand-written shim citing bm_inv via
{bm_hyp_name}.
-/
import SynthLean.Basic
open SynthLean

axiom count_eq : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int), (∀ v : Int, ((count_eq A 0 v) = 0))
axiom user_axiom_1 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A (k + 1) v) = ((count_eq A k v) + (if ((A k) = v) then 1 else 0)))))
axiom user_axiom_2 : ∀ (A : Int → Int), (∀ k v : Int, ((k ≥ 0) → ((count_eq A k v) ≥ 0)))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n candidate i cnt : Int)
    (A : Int → Int)
    (h_pre : ((n ≥ 1) ∧ (∃ v : Int, ((count_eq A n v) > (n / 2)))))
{binders_block}
    (h_g_loop : (i < n)) :
    ((cnt = 0)) ∨ ((cnt > 0)) := by
  have h_bm := {bm_hyp_name} candidate
  -- h_bm : cnt + count_eq A i candidate ≥ count_eq A i candidate
  have h_cnt_nn : cnt ≥ 0 := by linarith
  omega

end SynthLean.VerifyTmp
"""


def gen(hash_id: str) -> str:
    info = HYP_TABLE[hash_id]
    binders = info["binders"]
    bm_hyp = info["bm_hyp"]
    binders_lines = "\n".join(
        f"    ({name} : {typ})" for name, typ in binders
    )
    return _TEMPLATE.format(
        hash=hash_id,
        bm_hyp_name=bm_hyp,
        binders_block=binders_lines,
    )


if __name__ == "__main__":
    import pathlib
    base = pathlib.Path(__file__).parent.parent / "lean/SynthLean/Y2Corpus/majority_element"
    for h in HYP_TABLE:
        out = base / f"sc1_fallthrough_{h}.solved.lean"
        out.write_text(gen(h))
        print(f"wrote {out}")
