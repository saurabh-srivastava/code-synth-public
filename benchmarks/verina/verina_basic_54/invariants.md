# Discovered invariant + ranking — verina_basic_54

```
invariant L0: ForAll(lambda p, q: Implies(0 <= p and p < i and 0 <= q and q < m, r <= ((A[p] - B[q]) if A[p] >= B[q] else (B[q] - A[p])))) ∧ 0 <= wi and wi < n and 0 <= wj and wj < m and r == ((A[wi] - B[wj]) if A[wi] >= B[wj] else (B[wj] - A[wi])) ∧ 0 <= i and i <= n and n >= 1 and m >= 1
ranking   L0: n - i
invariant L1: ForAll(lambda p, q: Implies(0 <= p and 0 <= q and q < m and ((p < i) or (p == i and q < j)), r <= ((A[p] - B[q]) if A[p] >= B[q] else (B[q] - A[p])))) ∧ 0 <= wi and wi < n and 0 <= wj and wj < m and r == ((A[wi] - B[wj]) if A[wi] >= B[wj] else (B[wj] - A[wi])) ∧ 0 <= j and j <= m and 0 <= i and i < n and n >= 1 and m >= 1
ranking   L1: m - j
```
