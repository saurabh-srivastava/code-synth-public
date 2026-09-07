"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : n >= 0
   post : s == digitSum(n)
"""

def synth(n: int) -> int:
    s = 0
    m = 0

    s, m = 0, n
    # invariant L0: s + digitSum(m) == digitSum(n)
    # ranking   L0: m
    while m != 0:
        s, m = s + m % 10, m / 10
    pass  # skip
    return s
