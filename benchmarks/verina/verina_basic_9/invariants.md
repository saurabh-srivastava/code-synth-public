# Discovered invariant + ranking — verina_basic_9

```
invariant L0: 0 <= i ∧ i <= na ∧ na >= 0 ∧ nb >= 0 ∧ ((found == 1) and Exists(lambda p: 0 <= p and p < i and Exists(lambda j: 0 <= j and j < nb and a[p] == b[j]))) or ((found == 0) and ForAll(lambda p: Implies(0 <= p and p < i, ForAll(lambda j: Implies(0 <= j and j < nb, a[p] != b[j])))))
ranking   L0: na - i
```
