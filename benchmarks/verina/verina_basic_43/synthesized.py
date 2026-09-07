"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : 15*s == n*(2*n + 1)*(7 + 24*n*n*n - 12*n*n - 14*n)
"""

def synth(n: int) -> int:
    s = 0
    i = 0

    s, i = 0, 0
    # invariant L0: 15*s == i*(2*i + 1)*(7 + 24*i*i*i - 12*i*i - 14*i)
    # ranking   L0: n - i
    while i < n:
        s, i = s + (2 * i + 1) * (2 * i + 1) * (2 * i + 1) * (2 * i + 1), i + 1
    pass  # skip
    return s
