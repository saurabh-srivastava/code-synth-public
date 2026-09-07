"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : p == uprod(A, n)
"""

def synth(A: list[int], n: int) -> int:
    p = 0
    i = 0

    p, i = 1, 0
    # invariant L0: p == uprod(A, i)
    # ranking   L0: n - i
    while i < n:
        if seen(A, i) == 0:
            p, i = p * A[i], i + 1
        elif seen(A, i) != 0:
            i = i + 1
    pass  # skip
    return p
