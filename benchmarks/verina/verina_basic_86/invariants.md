# Discovered invariant + ranking — verina_basic_86

```
invariant L0: 0 <= i ∧ i <= n ∧ n >= 0 ∧ ForAll(lambda k: Implies(0 <= k and k < i, B[k] == A[(k + offset) % n]))
ranking   L0: n - i
```
