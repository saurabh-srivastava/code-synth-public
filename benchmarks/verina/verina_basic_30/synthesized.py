"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n > 0 and ForAll(lambda k: Implies(0 <= k and k < n, B[k] != 0))
   post : ForAll(lambda k: Implies(0 <= k and k < n, R[k] == A[k] % B[k]))
"""

def synth(A: list[int], B: list[int], R: list[int], n: int) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n:
        R[i] = A[i] % B[i]
        i = i + 1
    pass  # skip
