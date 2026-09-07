"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : k >= 1 and k <= n
   post : r == A[k - 1]
"""

def synth(A: list[int], k: int, n: int) -> int:
    r = 0

    r = A[k - 1]
    return r
