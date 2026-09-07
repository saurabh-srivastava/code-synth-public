# Discovered invariant + ranking — verina_basic_74

```
invariant L0: 1 <= i ∧ i <= n ∧ n >= 1 ∧ ForAll(lambda k: Implies(0 <= k and k < i, A[k] <= result)) ∧ Exists(lambda k: 0 <= k and k < i and A[k] == result)
ranking   L0: n - i
```
