"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : (m <= a) and (m <= b) and (m <= c) and ((m == a) or (m == b) or (m == c))
"""

def synth(a: int, b: int, c: int) -> int:
    m = 0

    if a <= b and a <= c:
        m = a
    elif b <= a and b <= c:
        m = b
    elif c <= a and c <= b:
        m = c
    return m
