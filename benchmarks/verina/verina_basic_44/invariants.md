# Discovered invariant + ranking — verina_basic_44

```
invariant L0: 0 <= i ∧ i <= n ∧ n >= 0 ∧ ((flag == 1) and  ForAll(lambda k: Implies(0 <= k and k < i, ((k % 2 != 1) or (A[k] % 2 == 1))))) or ((flag == 0) and  Exists(lambda k: 0 <= k and k < i and ((k % 2 == 1) and (A[k] % 2 != 1))))
ranking   L0: n - i
```
