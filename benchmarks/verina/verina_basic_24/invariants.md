# Discovered invariant + ranking — verina_basic_24

```
invariant L0: 0 <= d ∧ d <= n ∧ n > 1 ∧ ForAll(lambda k: Implies(0 <= k and k < d, A[k] % 2 == A[0] % 2)) ∧ Exists(lambda k: d <= k and k < n and A[k] % 2 != A[0] % 2)
ranking   L0: n - d
```
