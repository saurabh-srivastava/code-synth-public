"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : ((result == 1) and  Exists(lambda k: 0 <= k and k < n - 1 and A[k] + 1 == A[k + 1])) or ((result == 0) and  ForAll(lambda k: Implies(0 <= k and k < n - 1, A[k] + 1 != A[k + 1])))
"""

def synth(A: list[int], n: int) -> int:
    result = 0
    flag = 0
    i = 0

    flag, i = 0, 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n - 1:
        if A[i] + 1 == A[i + 1]:
            flag, i = 1, i + 1
        elif A[i] + 1 != A[i + 1]:
            i = i + 1
    result = flag
    return result
