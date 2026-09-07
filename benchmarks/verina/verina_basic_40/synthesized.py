"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 2 and Exists(lambda p, q: 0 <= p and p < n and 0 <= q and q < n and A[p] != A[q])
   post : Exists(lambda i: 0 <= i and i < n and A[i] == result) and Exists(lambda j: 0 <= j and j < n and A[j] < result and   ForAll(lambda k: Implies(0 <= k and k < n and A[k] != A[j],                            A[k] >= result)))
"""

def synth(A: list[int], n: int) -> int:
    result = 0
    m = 0
    sm = 0
    found = 0
    i = 0

    m, sm, found, i = A[0], A[0], 0, 1
    # invariant L0: ((found == 0) and  ForAll(lambda k: Implies(0 <= k and k < i, A[k] == m))) or ((found == 1) and (m < sm) and  ForAll(lambda k: Implies(0 <= k and k < i,                           A[k] == m or A[k] >= sm)) and  Exists(lambda k: 0 <= k and k < i and A[k] == m) and  Exists(lambda k: 0 <= k and k < i and A[k] == sm))
    # ranking   L0: n - i
    while i < n:
        if A[i] < m:
            m, sm, found, i = A[i], m, 1, i + 1
        elif A[i] > m:
            sm, found, i = A[i] if found == 0 or A[i] < sm else sm, 1, i + 1
        elif A[i] == m:
            i = i + 1
    result = sm
    return result
