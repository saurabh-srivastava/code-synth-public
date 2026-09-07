"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : 2 * avg == a + b - ((a + b) % 2)
"""

def synth(a: int, b: int) -> int:
    avg = 0

    avg = (a + b) / 2
    return avg
