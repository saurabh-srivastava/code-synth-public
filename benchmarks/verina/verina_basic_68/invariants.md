# Discovered invariant + ranking — verina_basic_68

```
invariant L0: 0 <= res ∧ res <= n ∧ n >= 0 ∧ ForAll(lambda k: Implies(0 <= k and k < res, A[k] != e))
ranking   L0: n - res
```
