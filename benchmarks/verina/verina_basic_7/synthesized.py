"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : result == (n * (2*n - 1) * (2*n + 1)) / 3
"""

def synth(n: int) -> int:
    result = 0

    result = n * (2 * n - 1) * (2 * n + 1) / 3
    return result
