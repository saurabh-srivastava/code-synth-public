"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : (d >= 0) and (d < 10) and ((n % 10) - d == 0 and d - (n % 10) == 0)
"""

def synth(n: int) -> int:
    d = 0

    d = n % 10
    return d
