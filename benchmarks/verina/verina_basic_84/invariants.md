# Discovered invariant + ranking — verina_basic_84

```
invariant L0: 0 <= i ∧ i <= n ∧ ForAll(lambda j: Implies(0 <= j and j < i, ((A[j] > k and B[j] == -1) or  (A[j] <= k and B[j] == A[j]))))
ranking   L0: n - i
```
