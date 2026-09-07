"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : Implies(result == 1, Exists(lambda i: i >= 0 and i*i == n)) and Implies(Exists(lambda i: i >= 0 and i*i == n), result == 1)
"""

def synth(n: int) -> int:
    result = 0
    r = 0

    r = 0
    # invariant L0: r*r <= n
    # ranking   L0: n - r*r
    while (r + 1) * (r + 1) <= n:
        r = r + 1
    result = 1 if r * r == n else 0
    return result
