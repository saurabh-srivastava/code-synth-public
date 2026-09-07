/-
fib's chain-bundle (post) obligation for chosen τ =
{a=fib(i), b=fib(i+1), 0≤i, i≤n}.

The exit-of-loop state has primed vars (a', b', i') with τ
holding; skip transition writes f' = a'.  Goal: f' = fib n.

Argument:
  - From h_tau_3 (i' ≤ n) and h_not_g (¬(i' < n)) and h_tau_2
    (0 ≤ i'): i' = n.
  - h_skip_f: f' = a'.  h_tau_0: a' = fib(i').
  - Substituting: f' = a' = fib(i') = fib(n).
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
theorem sc4_fallthrough
    (n f a b i : Int)
    (f' a' b' i' : Int)
    (h_pre : (n ≥ 0))
    (h_tau_0 : (a' = (fib i')))
    (h_tau_1 : (b' = (fib (i' + 1))))
    (h_tau_2 : (0 ≤ i'))
    (h_tau_3 : (i' ≤ n))
    (h_not_g : ¬ ((i' < n)))
    (h_skip_f : f' = a') :
    (f' = (fib n)) := by
  have h_i : i' = n := by omega
  rw [h_skip_f, h_tau_0, h_i]

end SynthLean.VerifyTmp
