/-
fib's loop-inductive obligation for chosen τ =
{a=fib(i), b=fib(i+1), 0≤i, i≤n}.

After substituting the transitions (a' = b, b' = a + b, i' = i + 1),
the four conjuncts reduce to:
  1. b = fib(i + 1)         — direct from h_tau_1.
  2. a + b = fib(i + 2)      — apply user_axiom_2 at k = i (precondition
                                i ≥ 0 from h_tau_2), giving
                                fib(i+2) = fib(i+1) + fib(i) = b + a.
  3. 0 ≤ i + 1              — omega from h_tau_2.
  4. i + 1 ≤ n              — omega from h_guard (i < n).
-/
import SynthLean.Basic
open SynthLean

axiom fib : Int → Int
axiom user_axiom_0 : ((fib 0) = 0)
axiom user_axiom_1 : ((fib 1) = 1)
axiom user_axiom_2 :
  (∀ k : Int, ((k ≥ 0) → ((fib (k + 2)) = ((fib (k + 1)) + (fib k)))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc1_fallthrough
    (n f a b i : Int)
    (a' b' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (a = (fib i)))
    (h_tau_1 : (b = (fib (i + 1))))
    (h_tau_2 : (0 ≤ i))
    (h_tau_3 : (i ≤ n))
    (h_guard : (i < n))
    (h_trans_a : a' = b)
    (h_trans_b : b' = (a + b))
    (h_trans_i : i' = (i + 1)) :
    ((a' = (fib i'))) ∧ ((b' = (fib (i' + 1)))) ∧ ((0 ≤ i')) ∧ ((i' ≤ n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Conjunct 1: a' = fib i'.  From h_trans_a: a' = b.  From h_tau_1: b = fib(i+1).
  -- From h_trans_i: i' = i+1.
  · rw [h_trans_a, h_tau_1, h_trans_i]
  -- Conjunct 2: b' = fib (i' + 1).  b' = a + b (h_trans_b).
  -- fib(i' + 1) = fib(i + 2) since i' = i + 1.  Apply user_axiom_2.
  · have h_rec : fib (i + 2) = fib (i + 1) + fib i :=
      user_axiom_2 i h_tau_2
    rw [h_trans_b, h_trans_i]
    have h_eq : i + 1 + 1 = i + 2 := by ring
    rw [h_eq, h_rec, h_tau_0, h_tau_1]
    ring
  · -- 0 ≤ i'
    rw [h_trans_i]; omega
  · -- i' ≤ n
    rw [h_trans_i]; omega

end SynthLean.VerifyTmp
