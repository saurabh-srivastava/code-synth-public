"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (n >= 1) and ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))
   post : (A[0] == B[n - 1]) and (A[n - 1] == B[0]) and ForAll(lambda k: Implies(0 < k and k < n - 1, A[k] == B[k]))
"""

def synth(A: list[int], B: list[int], n: int) -> None:
    A[0], A[n - 1] = A[n - 1], A[0]
