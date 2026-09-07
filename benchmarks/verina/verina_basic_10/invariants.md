# Discovered invariant + ranking — verina_basic_10

```
invariant L0: 0 <= i ∧ i <= n ∧ n >= 0 ∧ ((flag == 1) and  ForAll(lambda k: Implies(0 <= k and k < i, t > A[k]))) or ((flag == 0) and  Exists(lambda k: 0 <= k and k < i and t <= A[k]))
ranking   L0: n - i
```
