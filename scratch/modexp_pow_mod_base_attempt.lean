/-
Scratch: pow_mod_base lemma for modexp Tier-1.

Lemma: ∀ x m k, m ≥ 1 ∧ k ≥ 0 → pow x k % m = pow (x % m) k % m.

Proof: induction on k starting from 0.
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.modular_exponentiation.Helpers
open SynthLean

theorem pow_mod_base_attempt :
    ∀ (x m k : Int), m ≥ 1 → k ≥ 0 → pow x k % m = pow (x % m) k % m := by
  intro x m k hm hk
  induction k, hk using Int.le_induction with
  | base =>
    rw [user_axiom_0, user_axiom_0]
  | succ k hk ih =>
    have hm_pos : m > 0 := by omega
    rw [user_axiom_1 x k hk, user_axiom_1 (x % m) k hk]
    rw [user_axiom_3 x (pow x k) m hm]
    rw [ih]
    -- Goal: ((x % m) * (pow (x % m) k % m)) % m = ((x % m) * pow (x % m) k) % m
    -- Apply axiom_3 in reverse: ((a % m) * b % m) % m → (a * b) % m? Actually
    -- ((x % m) * pow (x%m) k) % m = ((x%m) % m * (pow (x%m) k % m)) % m
    -- = ((x % m) * (pow (x%m) k % m)) % m  by emod_emod_of_pos.
    rw [user_axiom_3 (x % m) (pow (x % m) k) m hm]
    congr 1
    congr 1
    exact (Int.emod_emod_of_dvd _ (dvd_refl m)).symm
