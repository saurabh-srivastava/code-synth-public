"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 1
   post : result + arrmin(A, n) == arrmax(A, n)
"""

def synth(A: list[int], n: int) -> int:
    result = 0
    minVal = 0
    maxVal = 0
    i = 0

    minVal, maxVal, i = A[0], A[0], 0
    # invariant L0: minVal == arrmin(A, i)
    # ranking   L0: n - i
    while i < n:
        minVal, maxVal, i = A[i] if A[i] < minVal else minVal, A[i] if A[i] > maxVal else maxVal, i + 1
    result = maxVal - minVal
    return result
