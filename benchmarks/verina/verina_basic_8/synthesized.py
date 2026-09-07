"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : (m <= a) and (m <= b) and ((m == a) or (m == b))
"""

def synth(a: int, b: int) -> int:
    m = 0

    if a <= b:
        m = a
    elif b <= a:
        m = b
    return m
