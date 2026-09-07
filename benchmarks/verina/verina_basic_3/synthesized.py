"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : Implies((n % 11 == 0), result == 1) and Implies(not (n % 11 == 0), result == 0)
"""

def synth(n: int) -> int:
    result = 0

    if n % 11 == 0:
        result = 1
    elif n % 11 != 0:
        result = 0
    return result
