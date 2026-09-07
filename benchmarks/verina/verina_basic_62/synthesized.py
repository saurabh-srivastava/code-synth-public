"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : (res == -1 or (res >= 0 and res < n)) and Implies(res != -1,   (A[res] == key) and   ForAll(lambda k: Implies(0 <= k and k < res,   A[k] != key))) and Implies(res == -1,   ForAll(lambda k: Implies(0 <= k and k < n,   A[k] != key)))
"""

def synth(A: list[int], n: int, key: int) -> int:
    res = 0
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n and A[i] != key:
        i = i + 1
    if i >= n:
        res = -1
    elif i < n:
        res = i
    return res
