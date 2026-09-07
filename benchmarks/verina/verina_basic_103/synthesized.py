"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (n >= 8) and ForAll(lambda k: Implies(0 <= k and k < n, B[k] == A[k]))
   post : (A[4] == B[4] + 3) and (A[7] == 516) and ForAll(lambda k: Implies(0 <= k and k < n and k != 4 and k != 7, A[k] == B[k]))
"""

def synth(A: list[int], B: list[int], n: int) -> None:
    A[4], A[7] = A[4] + 3, 516
