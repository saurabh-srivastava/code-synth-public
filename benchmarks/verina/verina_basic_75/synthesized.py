"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 1
   post : ForAll(lambda k: Implies(0 <= k and k < n, m <= A[k])) and Exists(lambda k: 0 <= k and k < n and m == A[k])
"""

def synth(A: list[int], n: int) -> int:
    m = 0
    i = 0

    m, i = A[0], 1
    # invariant L0: 1 <= i
    # ranking   L0: n - i
    while i < n:
        if A[i] < m:
            m, i = A[i], i + 1
        elif A[i] >= m:
            i = i + 1
    return m
