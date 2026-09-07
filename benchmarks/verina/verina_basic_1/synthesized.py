"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : Implies(((a < 0 and b > 0) or (a > 0 and b < 0)), result == 1) and Implies(not ((a < 0 and b > 0) or (a > 0 and b < 0)), result == 0)
"""

def synth(a: int, b: int) -> int:
    result = 0

    if a * b < 0:
        result = 1
    elif a * b >= 0:
        result = 0
    return result
