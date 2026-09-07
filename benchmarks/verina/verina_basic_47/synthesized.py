"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 1
   post : result == sum(A, n)
"""

def synth(A: list[int], n: int) -> int:
    result = 0
    i = 0

    result, i = 0, 0
    # invariant L0: 0 <= i
    # ranking   L0: n - i
    while i < n:
        result, i = result + A[i], i + 1
    pass  # skip
    return result
