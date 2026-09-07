"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : (r // 3 == x) and (r // 3 * 3 == r)
"""

def synth(x: int) -> int:
    r = 0

    r = 3 * x
    return r
