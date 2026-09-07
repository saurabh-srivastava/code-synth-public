"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 1
   post : ForAll(lambda k: Implies(0 <= k and k < n, A[k] <= result)) and Exists(lambda k: 0 <= k and k < n and A[k] == result)
"""

def synth(A: list[int], n: int) -> int:
    result = 0
    i = 0

    result, i = A[0], 1
    # invariant L0: 1 <= i
    # ranking   L0: n - i
    while i < n:
        if A[i] > result:
            result, i = A[i], i + 1
        elif A[i] <= result:
            i = i + 1
    return result
