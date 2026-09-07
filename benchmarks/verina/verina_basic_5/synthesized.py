"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : (p - a*b == 0) and (a*b - p == 0)
"""

def synth(a: int, b: int) -> int:
    p = 0

    p = a * b
    return p
