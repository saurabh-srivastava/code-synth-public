# Discovered invariant + ranking — verina_basic_41

```
invariant L0: 0 <= i ∧ i <= n ∧ n >= 0 ∧ ((flag == 1) and  ForAll(lambda k: Implies(0 <= k and k < i, A[k] == A[0]))) or ((flag == 0) and  Exists(lambda k: 0 <= k and k < i and A[k] != A[0]))
ranking   L0: n - i
```
