# Discovered invariant + ranking — verina_basic_83

```
invariant L0: 0 <= i ∧ i <= na + nb ∧ na >= 0 ∧ nb >= 0 ∧ ForAll(lambda k: Implies(0 <= k and k < na and k < i, C[k] == A[k])) ∧ ForAll(lambda k: Implies(0 <= k and k < nb and k + na < i, C[k + na] == B[k]))
ranking   L0: na + nb - i
```
