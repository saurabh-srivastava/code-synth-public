"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (0 <= k) and (k < n)
   post : ForAll(lambda j: Implies(0 <= j and j < k, B[j] == A[j])) and ForAll(lambda j: Implies(k <= j and j < n - 1, B[j] == A[j + 1]))
"""

def synth(A: list[int], B: list[int], n: int, k: int) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - 1 - i
    while i < n - 1:
        if i < k:
            B[i] = A[i]
            i = i + 1
        elif i >= k:
            B[i] = A[i + 1]
            i = i + 1
    pass  # skip
