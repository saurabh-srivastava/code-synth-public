# Discovered invariant + ranking — verina_basic_15

```
invariant L0: 0 <= i ∧ i <= n ∧ n >= 0 ∧ ((flag == 1) and  Exists(lambda k: 0 <= k and k < n - 1 and A[k] + 1 == A[k + 1])) or ((flag == 0) and  ForAll(lambda k: Implies(0 <= k and k < i, A[k] + 1 != A[k + 1] or k == n - 1)))
ranking   L0: n - i
```
