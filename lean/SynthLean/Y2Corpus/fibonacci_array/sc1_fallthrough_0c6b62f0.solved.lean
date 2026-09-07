/-
fibonacci_array's loop-inductive obligation for chosen τ =
{2 ≤ i, i ≤ n, ∀k. 0 ≤ k < i → C k = fib k}.

Body transition: C' = store C i (C(i-1) + C(i-2)); i' = i + 1.

The three conjuncts at body_out:
  1. 2 ≤ i+1                 — omega from h_tau_0.
  2. i+1 ≤ n                  — omega from h_guard.
  3. ∀k, 0 ≤ k < i+1 → C' k = fib k:
     Split on k < i vs k = i:
       k < i:  C' k = C k    (store preserves k ≠ i)
                    = fib k   (h_tau_2 at k).
       k = i:  C' i = C(i-1) + C(i-2)
                    = fib(i-1) + fib(i-2)   (h_tau_2 at i-1, i-2;
                                              i ≥ 2 ⇒ i-2, i-1 ∈ [0, i))
                    = fib((i-2)+1) + fib(i-2)
                    = fib((i-2)+2)          (user_axiom_2 at k = i-2,
                                              precondition i-2 ≥ 0)
                    = fib i.

The Pre-state's `C` variable is `Int → Int` because the IR
encodes arrays as Z3 ArrayRef; the translator lifts them to
`Int → Int` for the Lean obligation.
-/
import SynthLean.Core
open SynthLean

axiom fib : Int → Int
axiom user_axiom_0 : ((fib 0) = 0)
axiom user_axiom_1 : ((fib 1) = 1)
axiom user_axiom_2 :
  (∀ k : Int, ((k ≥ 0) → ((fib (k + 2)) = ((fib (k + 1)) + (fib k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n i : Int)
    (C : Int → Int)
    (i' : Int)
    (C' : Int → Int)
    (h_pre : (n ≥ 2))
    (h_tau_0 : (2 ≤ i))
    (h_tau_1 : (i ≤ n))
    (h_tau_2 : (∀ (k : Int), (((0 ≤ k) ∧ (k < i)) → ((C k) = (fib k)))))
    (h_guard : (i < n))
    (h_trans_C : C' = (store C i ((C (i - 1)) + (C (i - 2)))))
    (h_trans_i : i' = (i + 1)) :
    ((2 ≤ i')) ∧ ((i' ≤ n)) ∧ ((∀ (k : Int), (((0 ≤ k) ∧ (k < i')) → ((C' k) = (fib k))))) := by
  subst h_trans_C h_trans_i
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · -- ∀ k, 0 ≤ k < i+1 → store C i (C(i-1)+C(i-2)) k = fib k
    intro k hk
    obtain ⟨hk_lo, hk_hi⟩ := hk
    -- Split: k = i  vs  k ≠ i.
    by_cases h_eq : k = i
    · -- k = i: store at i.  Use recurrence at i-2.
      subst h_eq
      have h_ci1 : C (k - 1) = fib (k - 1) := h_tau_2 (k - 1) ⟨by omega, by omega⟩
      have h_ci2 : C (k - 2) = fib (k - 2) := h_tau_2 (k - 2) ⟨by omega, by omega⟩
      have h_rec : fib ((k - 2) + 2) = fib ((k - 2) + 1) + fib (k - 2) :=
        user_axiom_2 (k - 2) (by omega)
      have h_idx1 : (k - 2) + 2 = k := by omega
      have h_idx2 : (k - 2) + 1 = k - 1 := by omega
      rw [h_idx1, h_idx2] at h_rec
      -- h_rec : fib k = fib (k - 1) + fib (k - 2)
      -- Goal: store C k (C(k-1) + C(k-2)) k = fib k
      show (store C k ((C (k - 1)) + (C (k - 2)))) k = fib k
      have h_store_at : (store C k ((C (k - 1)) + (C (k - 2)))) k =
                         (C (k - 1)) + (C (k - 2)) := by
        simp [store]
      rw [h_store_at, h_ci1, h_ci2, h_rec]
    · -- k ≠ i: store transparent — store at k = C k.
      show (store C i ((C (i - 1)) + (C (i - 2)))) k = fib k
      have h_store_off : (store C i ((C (i - 1)) + (C (i - 2)))) k = C k := by
        simp [store, h_eq]
      rw [h_store_off]
      exact h_tau_2 k ⟨hk_lo, by omega⟩

end SynthLean.VerifyTmp
