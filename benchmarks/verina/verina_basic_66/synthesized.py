"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : (r == 1) == Exists(lambda k: x == 2 * k)
"""

def synth(x: int) -> int:
    r = 0

    if x % 2 == 0:
        r = 1
    elif x % 2 != 0:
        r = 0
    return r
