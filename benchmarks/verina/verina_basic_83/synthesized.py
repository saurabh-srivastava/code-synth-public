"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : na >= 0 and nb >= 0
   post : ForAll(lambda k: Implies(0 <= k and k < na, C[k] == A[k])) and ForAll(lambda k: Implies(0 <= k and k < nb, C[k + na] == B[k]))
"""

def synth(A: list[int], B: list[int], C: list[int], na: int, nb: int) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: na + nb - i
    while i < na + nb:
        C[i] = A[i] if i < na else B[i - na]
        i = i + 1
    pass  # skip
