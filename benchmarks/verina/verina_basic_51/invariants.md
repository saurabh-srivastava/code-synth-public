# Discovered invariant + ranking — verina_basic_51

```
invariant L0: 0 <= idx ∧ idx <= n ∧ n >= 0 ∧ ForAll(lambda p, q: Implies( 0 <= p and p <= q and q < n, A[p] <= A[q])) ∧ ForAll(lambda k: Implies( 0 <= k and k < idx, A[k] < key))
ranking   L0: n - idx
```
