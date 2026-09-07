"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n > 1 and Exists(lambda t: 0 <= t and t < n and A[t] % 2 == 0) and Exists(lambda t: 0 <= t and t < n and A[t] % 2 != 0)
   post : (0 <= fe) and (fe < n) and (0 <= fo) and (fo < n) and (A[fe] % 2 == 0) and (A[fo] % 2 != 0) and (result == A[fe] - A[fo]) and ForAll(lambda k: Implies(0 <= k and k < fe, A[k] % 2 != 0)) and ForAll(lambda k: Implies(0 <= k and k < fo, A[k] % 2 == 0))
"""

def synth(A: list[int], n: int) -> int:
    result = 0
    d = 0
    fe = 0
    fo = 0

    d = 0
    # invariant L0: 0 <= d
    # ranking   L0: n - d
    while d < n and A[d] % 2 == A[0] % 2:
        d = d + 1
    if A[0] % 2 == 0:
        fe, fo, result = 0, d, A[0] - A[d]
    elif A[0] % 2 != 0:
        fe, fo, result = d, 0, A[d] - A[0]
    return result
