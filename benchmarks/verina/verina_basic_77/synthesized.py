"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (A == B) and (0 <= index1) and (index1 < m) and (0 <= index2) and (index2 < w) and (0 <= val)
   post : ForAll(lambda i: Implies(0 <= i and i < m and i != index1, A[i] == B[i])) and ForAll(lambda j: Implies(0 <= j and j < w and j != index2, A[index1][j] == B[index1][j])) and (A[index1][index2] == val)
"""

def synth(A: list[list[int]], B: list[list[int]], index1: int, index2: int, val: int, m: int, w: int) -> None:
    A[index1][index2] = val
