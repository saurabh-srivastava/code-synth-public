"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : true
   post : Implies((a == b), result == 1) and Implies(a != b, result == 0)
"""

def synth(a: int, b: int) -> int:
    result = 0

    if a == b:
        result = 1
    elif a != b:
        result = 0
    return result
