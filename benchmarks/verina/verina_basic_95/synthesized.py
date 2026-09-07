"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (0 <= i) and (i < n) and (0 <= j) and (j < n) and ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))
   post : (A[i] == B[j]) and (A[j] == B[i]) and ForAll(lambda k: Implies(0 <= k and k < n and k != i and k != j, A[k] == B[k]))
"""

def synth(A: list[int], B: list[int], i: int, j: int, n: int) -> None:
    A[i], A[j] = A[j], A[i]
