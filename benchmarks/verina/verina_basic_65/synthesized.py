"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : N >= 0
   post : r*r <= N and N < (r + 1)*(r + 1)
"""

def synth(N: int) -> int:
    r = 0

    r = 0
    # invariant L0: r*r <= N
    # ranking   L0: N - r
    while (r + 1) * (r + 1) <= N:
        r = r + 1
    return r
