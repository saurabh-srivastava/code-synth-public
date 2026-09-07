"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : ((count_occ(A, key, n) == 1) and (result == 1)) or ((count_occ(A, key, n) != 1) and (result == 0))
"""

def synth(A: list[int], n: int, key: int) -> int:
    result = 0
    c = 0
    i = 0

    c, i = 0, 0
    # invariant L0: c == count_occ(A, key, i)
    # ranking   L0: n - i
    while i < n:
        if A[i] == key:
            c, i = c + 1, i + 1
        elif A[i] != key:
            i = i + 1
    result = 1 if c == 1 else 0
    return result
