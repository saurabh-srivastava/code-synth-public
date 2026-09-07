"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0 and ForAll(lambda k: Implies(0 <= k and k + 1 < n, A[k] <= A[k + 1]))
   post : (res == -1 or res >= 0) and Implies(res >= 0,   (res < n) and (A[res] == target) and   ForAll(lambda k: Implies(0 <= k and k < res,   A[k] != target))) and Implies(res == -1,   ForAll(lambda k: Implies(0 <= k and k < n,   A[k] != target)))
"""

def synth(A: list[int], n: int, target: int) -> int:
    res = 0
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n and A[i] != target:
        i = i + 1
    if i >= n:
        res = -1
    elif i < n:
        res = i
    return res
