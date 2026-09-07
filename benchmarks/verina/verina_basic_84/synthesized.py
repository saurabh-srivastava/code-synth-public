"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : ForAll(lambda j: Implies(0 <= j and j < n, ((A[j] > k and B[j] == -1) or  (A[j] <= k and B[j] == A[j]))))
"""

def synth(A: list[int], B: list[int], n: int, k: int) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n:
        if A[i] > k:
            B[i] = -1
            i = i + 1
        elif A[i] <= k:
            B[i] = A[i]
            i = i + 1
    pass  # skip
