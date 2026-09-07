"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 1
   post : ForAll(lambda k: Implies(0 <= k and k < n - 1, B[k] == A[k + 1]))
"""

def synth(A: list[int], B: list[int], n: int) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - 1 - i
    while i < n - 1:
        B[i] = A[i + 1]
        i = i + 1
    pass  # skip
