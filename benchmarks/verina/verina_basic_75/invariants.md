# Discovered invariant + ranking — verina_basic_75

```
invariant L0: 1 <= i ∧ i <= n ∧ n >= 1 ∧ ForAll(lambda k: Implies(0 <= k and k < i, m <= A[k])) ∧ Exists(lambda k: 0 <= k and k < i and m == A[k])
ranking   L0: n - i
```
