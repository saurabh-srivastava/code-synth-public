"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 2
   post : Implies(result == 1, ForAll(lambda k: Implies(2 <= k and k < n, n % k != 0))) and Implies(result == 0, Exists(lambda k: 2 <= k and k < n and n % k == 0))
"""

def synth(n: int) -> int:
    result = 0
    flag = 0
    i = 0

    flag, i = 1, 2
    # invariant L0: 2 <= i
    # ranking   L0: n - i
    while i < n:
        if n % i == 0:
            flag, i = 0, i + 1
        elif n % i != 0:
            i = i + 1
    result = flag
    return result
