/-
modular_exponentiation Tier-3 helpers — RESEARCH.md §H.1.

These are algorithm-correctness theorems parameterized on the
τ atoms required to prove each constraint kind.  Each
.solved.lean shim file CITES one of these helpers (with the
appropriate hypotheses), rather than re-deriving the full
proof.  ONE helper per (algorithm, constraint-kind), N
shim files (one per τ-subset variant the synth enumerates).

Naming convention: `<algorithm>_<constraint-kind>` helper.

These helpers depend on the user's axioms for `pow` (declared
in each shim).  They use:
  - user_axiom_0: ∀ x. pow x 0 = 1
  - user_axiom_1: ∀ x k. k ≥ 0 → pow x (k+1) = x * pow x k
  - user_axiom_2: ∀ x k. k ≥ 0 → pow x (2k) = pow (x*x) k
  - user_axiom_3: ∀ x y m. m ≥ 1 → (x*y) % m = ((x%m)*(y%m)) % m
-/
import SynthLean.Basic
open SynthLean

axiom pow : Int → Int → Int
axiom user_axiom_0 : (∀ x : Int, ((pow x 0) = 1))
axiom user_axiom_1 : (∀ x k : Int, ((k ≥ 0) → ((pow x (k + 1)) = (x * (pow x k)))))
axiom user_axiom_2 : (∀ x k : Int, ((k ≥ 0) → ((pow x (2 * k)) = (pow (x * x) k))))
axiom user_axiom_3 : (∀ x y mm : Int, ((mm ≥ 1) → (((x * y) % mm) = (((x % mm) * (y % mm)) % mm))))

/-
Per-branch invariant-preservation axioms for the
modular_exponentiation safety inductive step.  Captures the
algorithm content: the modular-product invariant
  result * pow(base, exp) % m == pow(b, e) % m
is preserved across both halving branches.

Branch 0 (odd exp): result := (result * base) % m,
                    base := (base * base) % m, exp := exp / 2.
  Uses user_axiom_1 (pow recurrence) + user_axiom_3 (mod
  multiplication) to fold one factor of `base` into `result`.

Branch 1 (even exp): base := (base * base) % m, exp := exp / 2.
                     result unchanged.
  Uses user_axiom_2 (pow squaring identity: pow x (2k) =
  pow (x*x) k).  result' = result, so result-related conjuncts
  trivial.

τ@L0 atom indices:
  0: exp ≥ 0    2: pow_inv (modular product)
  1: m ≥ 1      3: result ≥ 0     4: result < m

For branch 1, the translator only primes vars the BRANCH
modifies (base', exp'), not the union — so `result'` is NOT a
bound var in that theorem.  The axiom mirrors this: result
appears unprimed in branch 1's conclusion.
-/
-- Auxiliary Tier-1 lemma: pow respects mod in the base.
-- Inductive proof on k ≥ 0 via Int.le_induction.  Uses axiom_1
-- (pow recurrence), axiom_3 (mod-mult), and emod_emod idempotence.
theorem pow_mod_base (x m k : Int) (hm : m ≥ 1) (hk : k ≥ 0) :
    pow x k % m = pow (x % m) k % m := by
  induction k, hk using Int.le_induction with
  | base =>
    rw [user_axiom_0, user_axiom_0]
  | succ k hk ih =>
    rw [user_axiom_1 x k hk, user_axiom_1 (x % m) k hk]
    rw [user_axiom_3 x (pow x k) m hm]
    rw [ih]
    rw [user_axiom_3 (x % m) (pow (x % m) k) m hm]
    congr 1
    congr 1
    exact (Int.emod_emod_of_dvd _ (dvd_refl m)).symm

-- Tier-1: odd-exponent half-step.
-- pow base exp = base * pow base (exp-1) = base * pow (base*base) ((exp-1)/2)
-- (axiom_1 + axiom_2 with k = (exp-1)/2 = exp/2 = exp' since exp odd).
-- Then (result * pow base exp) % m = (result * base * pow base' exp') % m
-- = (result' * pow base' exp') % m via axiom_3 + pow_mod_base.
theorem modexp_branch0_preserves_inv :
    ∀ (b e m result base exp result' base' exp' : Int),
      ((e ≥ 0) ∧ (m ≥ 1)) →
      (exp ≥ 0) →
      (m ≥ 1) →
      (((result * (pow base exp)) % m) = ((pow b e) % m)) →
      (result ≥ 0) →
      (result < m) →
      ((exp > 0) ∧ ((exp % 2) = 1)) →
      (result' = ((result * base) % m)) →
      (base' = ((base * base) % m)) →
      (exp' = (exp / 2)) →
      ((exp' ≥ 0)) ∧ ((m ≥ 1)) ∧
      ((((result' * (pow base' exp')) % m) = ((pow b e) % m))) ∧
      ((result' ≥ 0)) ∧ ((result' < m)) := by
  intro _ _ m result base exp result' base' exp'
  intro _ _ hm h_inv _ _ h_guard h_result_eq h_base_eq h_exp_eq
  obtain ⟨h_exp_pos, h_odd⟩ := h_guard
  have h_exp'_nn : exp' ≥ 0 := by rw [h_exp_eq]; omega
  -- exp = 2 * exp' + 1 (since exp odd).
  have h_exp_decomp : exp = 2 * exp' + 1 := by rw [h_exp_eq]; omega
  -- pow base exp = base * pow base (2 * exp') (axiom_1, exp - 1 = 2*exp').
  have h_pow_step : pow base exp = base * pow base (2 * exp') := by
    have h_arg : 2 * exp' + 1 = (2 * exp') + 1 := by ring
    rw [h_exp_decomp, h_arg]
    exact user_axiom_1 base (2 * exp') (by linarith)
  -- pow base (2 * exp') = pow (base*base) exp' (axiom_2).
  have h_pow_square : pow base (2 * exp') = pow (base * base) exp' :=
    user_axiom_2 base exp' h_exp'_nn
  have h_pow_eq : pow base exp = base * pow (base * base) exp' := by
    rw [h_pow_step, h_pow_square]
  have h_base_mod_eq : pow (base * base) exp' % m = pow base' exp' % m := by
    rw [h_base_eq]; exact pow_mod_base (base * base) m exp' hm h_exp'_nn
  refine ⟨h_exp'_nn, hm, ?_, ?_, ?_⟩
  -- Main: (result' * pow base' exp') % m = pow b e % m.
  · rw [h_result_eq]
    -- Show: ((result*base) % m * pow base' exp') % m = pow b e % m.
    -- Pivot via pow_mod_base + axiom_3 manipulations.
    have key : (result * base) % m * pow base' exp' % m
             = result * base * pow (base * base) exp' % m := by
      conv_lhs => rw [user_axiom_3 ((result * base) % m) (pow base' exp') m hm]
      conv_lhs => rw [Int.emod_emod_of_dvd (result * base) (dvd_refl m)]
      conv_lhs => rw [← h_base_mod_eq]
      rw [← user_axiom_3 (result * base) (pow (base * base) exp') m hm]
    rw [key]
    rw [show result * base * pow (base * base) exp'
          = result * (base * pow (base * base) exp') by ring]
    rw [← h_pow_eq]
    exact h_inv
  -- result' ≥ 0: from emod_nonneg.
  · rw [h_result_eq]
    exact Int.emod_nonneg _ (by omega : m ≠ 0)
  -- result' < m: from emod_lt_of_pos.
  · rw [h_result_eq]
    exact Int.emod_lt_of_pos _ (by omega : m > 0)

-- Tier-1: even-exponent half-step.  Uses axiom_2 (squaring
-- identity) + pow_mod_base (base preserves under mod).
theorem modexp_branch1_preserves_inv :
    ∀ (b e m result base exp base' exp' : Int),
      ((e ≥ 0) ∧ (m ≥ 1)) →
      (exp ≥ 0) →
      (m ≥ 1) →
      (((result * (pow base exp)) % m) = ((pow b e) % m)) →
      (result ≥ 0) →
      (result < m) →
      ((exp > 0) ∧ ((exp % 2) = 0)) →
      (base' = ((base * base) % m)) →
      (exp' = (exp / 2)) →
      ((exp' ≥ 0)) ∧ ((m ≥ 1)) ∧
      ((((result * (pow base' exp')) % m) = ((pow b e) % m))) ∧
      ((result ≥ 0)) ∧ ((result < m)) := by
  intro _ _ m result base exp base' exp'
  intro _ _ hm h_inv h_r_nn h_r_lt h_guard h_base_eq h_exp_eq
  obtain ⟨h_exp_pos, h_even⟩ := h_guard
  -- exp' ≥ 0: exp ≥ 0, exp/2 ≥ 0 for exp ≥ 0.
  have h_exp'_nn : exp' ≥ 0 := by rw [h_exp_eq]; omega
  -- exp = 2 * exp'.
  have h_exp_decomp : exp = 2 * exp' := by rw [h_exp_eq]; omega
  -- pow base exp = pow (base*base) exp'.
  have h_pow_eq : pow base exp = pow (base * base) exp' := by
    rw [h_exp_decomp]; exact user_axiom_2 base exp' h_exp'_nn
  -- pow_mod_base: pow (base*base) exp' % m = pow base' exp' % m.
  have h_base_mod_eq : pow (base * base) exp' % m = pow base' exp' % m := by
    rw [h_base_eq]; exact pow_mod_base (base * base) m exp' hm h_exp'_nn
  refine ⟨h_exp'_nn, hm, ?_, h_r_nn, h_r_lt⟩
  -- (result * pow base' exp') % m = (pow b e) % m
  rw [user_axiom_3 result (pow base' exp') m hm]
  rw [← h_base_mod_eq]
  rw [← user_axiom_3 result (pow (base * base) exp') m hm]
  rw [← h_pow_eq]
  exact h_inv

namespace SynthLean.ModExpHelpers

/-
Bundle-post helper (kind = safety-bundle-post, sc7).

Given the loop-exit state with the modular-product invariant
+ result in canonical [0, m) form, derive the post.

Required τ atoms (any τ-subset MUST include all of these for
the bundle-post to be provable):
  - exp_nn:   exp' ≥ 0
  - m_ge_1:   m ≥ 1
  - pow_inv:  (result' * pow base' exp') % m = pow b e % m
  - res_nn:   result' ≥ 0
  - res_lt_m: result' < m

Plus the loop-exit hypothesis:
  - h_not_g:  ¬ (exp' > 0)

Proof chain:
  1. exp' = 0  (from h_exp_nn + h_not_g via omega).
  2. pow base' 0 = 1  (user_axiom_0).
  3. result' * 1 % m = pow b e % m  (from h_pow_inv after step 2).
  4. result' % m = pow b e % m  (one_mul on step 3).
  5. result' % m = result'  (Int.emod_eq_of_lt from h_res_nn,
                             h_res_lt_m).
  6. result' = pow b e % m  (transitivity of 4 and 5).
-/
theorem post_from_inv
    (b e m result' base' exp' : Int)
    (h_exp_nn : exp' ≥ 0)
    (h_m : m ≥ 1)
    (h_pow_inv : ((result' * (pow base' exp')) % m) = ((pow b e) % m))
    (h_res_nn : result' ≥ 0)
    (h_res_lt_m : result' < m)
    (h_not_g : ¬ (exp' > 0)) :
    result' = ((pow b e) % m) := by
  have h_exp_eq : exp' = 0 := by omega
  have h_pow0 : pow base' 0 = 1 := user_axiom_0 base'
  rw [h_exp_eq, h_pow0, mul_one] at h_pow_inv
  have h_mod : result' % m = result' :=
    Int.emod_eq_of_lt h_res_nn h_res_lt_m
  rw [h_mod] at h_pow_inv
  exact h_pow_inv

end SynthLean.ModExpHelpers
