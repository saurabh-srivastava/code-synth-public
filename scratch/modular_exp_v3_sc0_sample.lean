/-
modular_exp v3 sc0 (entry-bundle) reference proof.

Init now: result' = 1 % m (NOT just 1).  This is the key
spec fix that closes the τ-atom gap from the v1/v2 runs.

The hard conjunct is the pow invariant:
  ((1 % m) * pow(b, e)) % m == pow(b, e) % m

Proof: by axiom 3 (modular product), this equals
  ((1 % m) % m * (pow(b, e) % m)) % m
  = (1 % m * pow(b, e) % m) % m   (since (1 % m) % m = 1 % m)
  = (1 * pow(b, e)) % m            (axiom 3 backwards)
  = pow(b, e) % m

Below is a representative proof for the full-τ goal.  Other
variants drop some conjuncts.
-/
import SynthLean.Basic
open SynthLean

axiom pow : Int → Int → Int
axiom user_axiom_0 : (∀ x : Int, ((pow x 0) = 1))
axiom user_axiom_1 : (∀ x k : Int, ((k ≥ 0) → ((pow x (k + 1)) = (x * (pow x k)))))
axiom user_axiom_2 : (∀ x k : Int, ((k ≥ 0) → ((pow x (2 * k)) = (pow (x * x) k))))
axiom user_axiom_3 : (∀ x y mm : Int, ((mm ≥ 1) → (((x * y) % mm) = (((x % mm) * (y % mm)) % mm))))

namespace SynthLean.VerifyTmp

set_option linter.unusedVariables false in
theorem sc0_sample
    (b e m result base exp : Int)
    (result' base' exp' : Int)
    (h_pre : ((e ≥ 0) ∧ (m ≥ 1)))
    (h_init_result : result' = (1 % m))
    (h_init_base : base' = b)
    (h_init_exp : exp' = e) :
    ((exp' ≥ 0)) ∧ ((m ≥ 1)) ∧
    ((((result' * (pow base' exp')) % m) = ((pow b e) % m))) ∧
    ((result' ≥ 0)) ∧ ((result' < m)) := by
  obtain ⟨h_e_nn, h_m⟩ := h_pre
  have h_m_ne : m ≠ 0 := by omega
  have h_m_pos : (0 : Int) < m := by omega
  subst_eqs
  refine ⟨h_e_nn, h_m, ?_, ?_, ?_⟩
  · -- (1 % m * pow b e) % m = pow b e % m
    -- Use axiom 3 forward + (1 % m) % m simplification.
    rw [user_axiom_3 (1 % m) (pow b e) m h_m]
    rw [Int.emod_emod_of_dvd _ (dvd_refl m)]
    rw [← user_axiom_3 1 (pow b e) m h_m]
    rw [one_mul]
  · -- 1 % m ≥ 0
    exact Int.emod_nonneg 1 h_m_ne
  · -- 1 % m < m
    exact Int.emod_lt_of_pos 1 h_m_pos

end SynthLean.VerifyTmp
