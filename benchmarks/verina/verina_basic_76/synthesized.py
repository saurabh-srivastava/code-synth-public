"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : ((x > y) or (result == x)) and ((x <= y) or (result == y))
"""

def synth(x: int, y: int) -> int:
    result = 0

    if x <= y:
        result = x
    elif x > y:
        result = y
    return result
