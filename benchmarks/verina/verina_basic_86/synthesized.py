"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (offset >= 0) and (n >= 0)
   post : ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[(k + offset) % n]))
"""

def synth(A: list[int], n: int, offset: int, B: list[int]) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n:
        B[i] = A[(i + offset) % n]
        i = i + 1
