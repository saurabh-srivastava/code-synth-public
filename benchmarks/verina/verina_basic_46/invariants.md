# Discovered invariant + ranking — verina_basic_46

```
invariant L0: pos == -1 or (0 <= pos and pos < i and A[pos] == elem) ∧ ForAll(lambda k: Implies(pos < k and k < i, A[k] != elem)) ∧ 0 <= i ∧ i <= n ∧ n >= 0
ranking   L0: n - i
```
