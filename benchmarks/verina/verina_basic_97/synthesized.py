"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (0 <= j) and (j < n) and ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))
   post : (A[j] == 60) and ForAll(lambda k: Implies(0 <= k and k < n and k != j, A[k] == B[k]))
"""

def synth(A: list[int], B: list[int], j: int, n: int) -> None:
    A[j] = 60
