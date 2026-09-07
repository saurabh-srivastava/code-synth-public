/-
Scratch: auxiliary lemmas for merge_two_sorted Tier-1 promotion.

  (1) is_sorted_eq_below : ∀ A B k. (∀ i, 0 ≤ i ∧ i < k → A i = B i)
                                   → is_sorted A k = is_sorted B k
  (2) is_sorted_store_unchanged : ∀ A k v m.  0 ≤ m ≤ k →
                                  is_sorted (store A k v) m = is_sorted A m
  (3) is_sorted_extract : ∀ A n k. is_sorted A n = 1 ∧ 1 ≤ k ∧ k < n →
                                   A (k-1) ≤ A k

We don't need a generic axiomatic `is_sorted` here — use the merge
benchmark's existing `is_sorted` UF and its mts_user_axiom_*.
-/
import SynthLean.Basic
import SynthLean.Y2Corpus.merge_two_sorted.Helpers
open SynthLean

-- Lemma 1: is_sorted depends only on positions < k.
theorem is_sorted_eq_below (A B : Int → Int) (k : Int) (hk : k ≥ 0)
    (h_agree : ∀ i : Int, 0 ≤ i → i < k → A i = B i) :
    is_sorted A k = is_sorted B k := by
  induction k, hk using Int.le_induction with
  | base => rw [mts_user_axiom_0, mts_user_axiom_0]
  | succ k hk ih =>
    by_cases hk1 : k = 0
    · subst hk1
      show is_sorted A 1 = is_sorted B 1
      rw [mts_user_axiom_3, mts_user_axiom_3]
    · have hk_ge1 : k ≥ 1 := by omega
      rw [mts_user_axiom_6 A k hk_ge1, mts_user_axiom_6 B k hk_ge1]
      -- Need to show ih + agreement at k-1, k.
      have ih_eq : is_sorted A k = is_sorted B k := ih (fun i h0 hk_ => h_agree i h0 (by omega))
      have hA_km1 : A (k - 1) = B (k - 1) := h_agree (k - 1) (by omega) (by omega)
      have hA_k : A k = B k := h_agree k (by omega) (by omega)
      rw [ih_eq, hA_km1, hA_k]

-- Lemma 2: store unchanged below the store index.
theorem is_sorted_store_unchanged (A : Int → Int) (k : Int) (v : Int) (m : Int)
    (hm : m ≥ 0) (hmk : m ≤ k) :
    is_sorted (store A k v) m = is_sorted A m := by
  apply is_sorted_eq_below _ _ _ hm
  intro i h0 hi
  unfold store
  have h_ne : i ≠ k := by omega
  simp [h_ne]

-- Lemma 3a: downward propagation of is_sorted.  Wraps axiom_6
-- by inducting on n - k (well-founded since both are bounded).
theorem is_sorted_down (A : Int → Int) (n k : Int) (hk : 1 ≤ k) (hkn : k ≤ n)
    (h_sorted_n : is_sorted A n = 1) : is_sorted A k = 1 := by
  -- Induct downward from n to k via `n - k`.  Use the strong
  -- induction principle via well-founded recursion on `(n - k).toNat`.
  have h_n_ge : n ≥ 1 := by omega
  -- Generalize by induction on m := n - k, starting from m = 0
  -- (n = k) and increasing.
  suffices h_aux : ∀ m : Nat, ∀ n_ : Int, k + m = n_ → k ≤ n_ →
                    is_sorted A n_ = 1 → is_sorted A k = 1 by
    exact h_aux (n - k).toNat n (by omega) hkn h_sorted_n
  intro m
  induction m with
  | zero =>
    intro n_ h_eq _ h_sn
    have : n_ = k := by omega
    rw [← this]; exact h_sn
  | succ m ih =>
    intro n_ h_eq hkn_ h_sn
    -- n_ = k + (m + 1).  Apply axiom_6 to extract is_sorted A (n_ - 1).
    have h_m1_ge1 : n_ - 1 ≥ 1 := by omega
    have h_axiom := mts_user_axiom_6 A (n_ - 1) (by omega)
    have h_n_eq : n_ - 1 + 1 = n_ := by omega
    rw [h_n_eq] at h_axiom
    rw [h_axiom] at h_sn
    -- h_sn : (if ... then 1 else 0) = 1.  Extract that is_sorted A (n_-1) = 1.
    by_cases hcond : (is_sorted A (n_ - 1) = 1) ∧ (A ((n_ - 1) - 1) ≤ A (n_ - 1))
    · have h_sub : is_sorted A (n_ - 1) = 1 := hcond.1
      exact ih (n_ - 1) (by omega) (by omega) h_sub
    · simp [hcond] at h_sn

-- Lemma 3: extract A[k-1] ≤ A[k] from is_sorted A n.
theorem is_sorted_extract (A : Int → Int) (n k : Int)
    (h_sorted : is_sorted A n = 1) (h_k_ge : 1 ≤ k) (h_k_lt : k < n) :
    A (k - 1) ≤ A k := by
  have h_sk1 : is_sorted A (k + 1) = 1 :=
    is_sorted_down A n (k + 1) (by omega) (by omega) h_sorted
  have h_axiom := mts_user_axiom_6 A k h_k_ge
  rw [h_axiom] at h_sk1
  by_cases hcond : (is_sorted A k = 1) ∧ (A (k - 1) ≤ A k)
  · exact hcond.2
  · simp [hcond] at h_sk1
