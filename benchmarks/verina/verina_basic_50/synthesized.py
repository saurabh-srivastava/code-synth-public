"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : Implies(x >= 0, result == x) and Implies(x < 0, x + result == 0)
"""

def synth(x: int) -> int:
    result = 0

    if x < 0:
        result = 0 - x
    elif x >= 0:
        result = x
    return result
