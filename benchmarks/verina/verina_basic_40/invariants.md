# Discovered invariant + ranking — verina_basic_40

```
invariant L0: ((found == 0) and  ForAll(lambda k: Implies(0 <= k and k < i, A[k] == m))) or ((found == 1) and (m < sm) and  ForAll(lambda k: Implies(0 <= k and k < i,                           A[k] == m or A[k] >= sm)) and  Exists(lambda k: 0 <= k and k < i and A[k] == m) and  Exists(lambda k: 0 <= k and k < i and A[k] == sm)) ∧ 1 <= i ∧ i <= n
ranking   L0: n - i
```
