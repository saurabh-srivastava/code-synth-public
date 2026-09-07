/-
verina_basic_80 (only_once) — chain-bundle post (sc7).
Bridges loop exit + final `result := (c == 1) ? 1 : 0` to the
postcondition `result ↔ count_occ(A,key,n) = 1`.

From i' ≤ n ∧ ¬(i' < n): i' = n, so h_tau_0 gives
c' = count_occ(A,key,n).  Case-split on c' = 1:
  * c' = 1 → count = 1 and (if c'=1 then 1 else 0) = 1  → left  disjunct.
  * c' ≠ 1 → count ≠ 1 and (if c'=1 then 1 else 0) = 0  → right disjunct.
-/
import SynthLean.Core
open SynthLean

axiom count_occ : (Int → Int) → Int → Int → Int
axiom user_axiom_0 : ∀ (A : Int → Int) (key : Int), ((count_occ A key 0) = 0)
axiom user_axiom_1 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) = key)) → ((count_occ A key (k + 1)) = ((count_occ A key k) + 1))))
axiom user_axiom_2 : ∀ (A : Int → Int) (key : Int), (∀ (k : Int), (((k ≥ 0) ∧ ((A k) ≠ key)) → ((count_occ A key (k + 1)) = (count_occ A key k))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem sc7_fallthrough
    (n key result c i : Int)
    (A : Int → Int)
    (result' c' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (c' = (count_occ A key i')))
    (h_tau_1 : (0 ≤ i'))
    (h_tau_2 : (i' ≤ n))
    (h_tau_3 : (n ≥ 0))
    (h_not_g : ¬ ((i' < n)))
    (h_skip_result : result' = (if (c' = 1) then 1 else 0)) :
    ((((count_occ A key n) = 1) ∧ (result' = 1)) ∨ (((count_occ A key n) ≠ 1) ∧ (result' = 0))) := by
  have h_i : i' = n := by omega
  rw [h_i] at h_tau_0
  -- h_tau_0 : c' = count_occ A key n
  by_cases hc : c' = 1
  · left
    refine ⟨?_, ?_⟩
    · rw [← h_tau_0]; exact hc
    · rw [h_skip_result, if_pos hc]
  · right
    refine ⟨?_, ?_⟩
    · rw [← h_tau_0]; exact hc
    · rw [h_skip_result, if_neg hc]

end SynthLean.VerifyTmp
