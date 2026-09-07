"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 1 and m >= 1
   post : Exists(lambda p, q: 0 <= p and p < n and 0 <= q and q < m and r == ((A[p] - B[q]) if A[p] >= B[q] else (B[q] - A[p]))) and ForAll(lambda p, q: Implies(0 <= p and p < n and 0 <= q and q < m, r <= ((A[p] - B[q]) if A[p] >= B[q] else (B[q] - A[p]))))
"""

def synth(A: list[int], B: list[int], n: int, m: int) -> int:
    r = 0
    i = 0
    j = 0
    wi = 0
    wj = 0

    r, i, wi, wj = A[0] - B[0] if A[0] >= B[0] else B[0] - A[0], 0, 0, 0
    # invariant L0: ForAll(lambda p, q: Implies(0 <= p and p < i and 0 <= q and q < m, r <= ((A[p] - B[q]) if A[p] >= B[q] else (B[q] - A[p]))))
    # ranking   L0: n - i
    while i < n:
        j = 0
        # invariant L1: ForAll(lambda p, q: Implies(0 <= p and 0 <= q and q < m and ((p < i) or (p == i and q < j)), r <= ((A[p] - B[q]) if A[p] >= B[q] else (B[q] - A[p]))))
        # ranking   L1: m - j
        while j < m:
            if (A[i] - B[j] if A[i] >= B[j] else B[j] - A[i]) < r:
                r, wi, wj, j = A[i] - B[j] if A[i] >= B[j] else B[j] - A[i], i, j, j + 1
            elif (A[i] - B[j] if A[i] >= B[j] else B[j] - A[i]) >= r:
                j = j + 1
        i = i + 1
    return r
