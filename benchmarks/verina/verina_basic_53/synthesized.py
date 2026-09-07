"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : N >= 0
   post : 2*s == N*(N + 1)
"""

def synth(N: int) -> int:
    s = 0
    i = 0

    s, i = 0, 0
    # invariant L0: 2*s == i*(i + 1)
    # ranking   L0: N - i
    while i < N:
        s, i = s + i + 1, i + 1
    pass  # skip
    return s
