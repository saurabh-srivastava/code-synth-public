"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (n >= 0) and ForAll(lambda p, q: Implies(  0 <= p and p <= q and q < n, A[p] <= A[q]))
   post : (0 <= idx) and (idx <= n) and ForAll(lambda k: Implies(0 <= k and k < idx,                          A[k] < key)) and ForAll(lambda k: Implies(idx <= k and k < n,                          A[k] >= key))
"""

def synth(A: list[int], n: int, key: int) -> int:
    idx = 0

    idx = 0
    # invariant L0: 0 <= idx
    # ranking   L0: n - idx
    while idx < n and A[idx] < key:
        idx = idx + 1
    return idx
