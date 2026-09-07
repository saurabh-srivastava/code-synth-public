"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : c == count_less(A, threshold, n)
"""

def synth(A: list[int], n: int, threshold: int) -> int:
    c = 0
    i = 0

    c, i = 0, 0
    # invariant L0: c == count_less(A, threshold, i)
    # ranking   L0: n - i
    while i < n:
        if A[i] < threshold:
            c, i = c + 1, i + 1
        elif A[i] >= threshold:
            i = i + 1
    pass  # skip
    return c
