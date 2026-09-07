"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0 and ForAll(lambda k: Implies(0 <= k and k < n - 1, A[k] <= A[k + 1]))
   post : (pos == -1 or pos >= 0) and Implies(pos >= 0,   (pos < n) and (A[pos] == elem) and   ForAll(lambda k: Implies(pos < k and k < n,                            A[k] != elem))) and Implies(pos == -1,   ForAll(lambda k: Implies(0 <= k and k < n,                            A[k] != elem)))
"""

def synth(A: list[int], n: int, elem: int) -> int:
    pos = 0
    i = 0

    pos, i = -1, 0
    # invariant L0: pos == -1 or (0 <= pos and pos < i and A[pos] == elem)
    # ranking   L0: n - i
    while i < n:
        if A[i] == elem:
            pos, i = i, i + 1
        elif A[i] != elem:
            i = i + 1
    pass  # skip
    return pos
