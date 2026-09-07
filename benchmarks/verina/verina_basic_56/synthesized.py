"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : (sStart >= 0) and (dStart >= 0) and (len >= 0) and ForAll(lambda k: D0[k] == dest[k])
   post : ForAll(lambda k: Implies(k < dStart, dest[k] == D0[k])) and ForAll(lambda k: Implies(dStart + len <= k, dest[k] == D0[k])) and ForAll(lambda k: Implies(0 <= k and k < len, dest[dStart + k] == src[sStart + k]))
"""

def synth(src: list[int], dest: list[int], D0: list[int], sStart: int, dStart: int, len: int) -> None:
    i = 0

    i = 0
    # invariant L0: 0 <= i
    # ranking   L0: len - i
    while i < len:
        dest[dStart + i] = src[sStart + i]
        i = i + 1
    pass  # skip
