"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : (res <= n) and ((res == n) or (A[res] == e)) and ForAll(lambda k: Implies(0 <= k and k < res, A[k] != e))
"""

def synth(A: list[int], n: int, e: int) -> int:
    res = 0

    res = 0
    # invariant L0: 0 <= res
    # ranking   L0: n - res
    while res < n and A[res] != e:
        res = res + 1
    return res
