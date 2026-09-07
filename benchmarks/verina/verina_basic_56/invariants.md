# Discovered invariant + ranking — verina_basic_56

```
invariant L0: 0 <= i ∧ i <= len ∧ ForAll(lambda k: Implies(0 <= k and k < i, dest[dStart + k] == src[sStart + k])) ∧ ForAll(lambda k: Implies(k < dStart, dest[k] == D0[k])) ∧ ForAll(lambda k: Implies(dStart + len <= k, dest[k] == D0[k]))
ranking   L0: len - i
```
