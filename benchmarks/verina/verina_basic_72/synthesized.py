"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : ForAll(lambda k: Implies(0 <= k and k < n, C[k] == A[k])) and (C[n] == b)
"""

def synth(A: list[int], C: list[int], n: int, b: int) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n:
        C[i] = A[i]
        i = i + 1
    C[n] = b
