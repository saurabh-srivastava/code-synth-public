"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : Implies(result == 1, (n % 2 == 0)) and Implies(result == 0, not (n % 2 == 0))
"""

def synth(n: int) -> int:
    result = 0

    if n % 2 == 0:
        result = 1
    elif n % 2 != 0:
        result = 0
    return result
