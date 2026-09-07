# Discovered invariant + ranking — verina_basic_29

```
invariant L0: 0 <= i ∧ i <= n - 1 ∧ 0 <= k ∧ k < n ∧ ForAll(lambda j: Implies(0 <= j and j < i and j < k, B[j] == A[j])) ∧ ForAll(lambda j: Implies(k <= j and j < i, B[j] == A[j + 1]))
ranking   L0: n - 1 - i
```
