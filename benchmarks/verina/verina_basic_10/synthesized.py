"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n > 0
   post : ((result == 1) and  ForAll(lambda k: Implies(0 <= k and k < n, t > A[k]))) or ((result == 0) and  Exists(lambda k: 0 <= k and k < n and t <= A[k]))
"""

def synth(A: list[int], n: int, t: int) -> int:
    result = 0
    flag = 0
    i = 0

    flag, i = 1, 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n:
        if t > A[i]:
            i = i + 1
        elif t <= A[i]:
            flag, i = 0, i + 1
    result = flag
    return result
