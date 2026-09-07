"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : result // 3 == x and result // 3 * 3 == result
"""

def synth(x: int) -> int:
    result = 0

    result = 3 * x
    return result
