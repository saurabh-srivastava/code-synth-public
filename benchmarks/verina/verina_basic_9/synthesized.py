"""Synthesized by Pragna-successor (proof-theoretic synthesis).

   pre  : na > 0 and nb > 0
   post : ((result == 1) and Exists(lambda p: 0 <= p and p < na and Exists(lambda j: 0 <= j and j < nb and a[p] == b[j]))) or ((result == 0) and ForAll(lambda p: Implies(0 <= p and p < na, ForAll(lambda j: Implies(0 <= j and j < nb, a[p] != b[j])))))
"""

def synth(a: list[int], b: list[int], na: int, nb: int) -> int:
    result = 0
    found = 0
    i = 0

    found, i = 0, 0
    # invariant L0: 0 <= i
    # ranking   L0: na - i
    while i < na:
        if None:
            found, i = 1, i + 1
        elif all((a[i] != b[j] for j in range(0, nb) if 0 <= j and j < nb)):
            i = i + 1
    result = found
    return result
