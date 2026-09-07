# Discovered invariant + ranking — verina_basic_28

```
invariant L0: 2 <= i ∧ i <= n ∧ n >= 2 ∧ ((flag == 1) and ForAll(lambda k: Implies(2 <= k and k < i, n % k != 0))) or ((flag == 0) and Exists(lambda k: 2 <= k and k < i and n % k == 0))
ranking   L0: n - i
```
