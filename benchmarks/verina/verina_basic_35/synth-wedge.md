# verina_basic_35 — SYNTH WEDGE

**MoveZeroesToEnd** — This task requires writing a Lean 4 method that rearranges an array of integers by moving all zero values to the end of the array. The method should ensure that the relative order of the non-zero elements remains the same, the overall size of the array is unchanged, and the number of zeroes in the array stays constant.

## Outcome

synth reached Lean dispatch and wedged on the first safety obligation (sc2, L0 branch 0).  The stable-partition (move-zeroes) invariant needs the `nz` compaction-index UF preserved across a quantified Store — the multiset/permutation E-matching cliff.

## Serialized data

```json
{
  "id": "verina_basic_35",
  "name": "MoveZeroesToEnd",
  "category": "synth-wedge",
  "verina_signature": {
    "name": "MoveZeroesToEnd",
    "parameters": [
      {
        "param_name": "arr",
        "param_type": "Array Int"
      }
    ],
    "return_type": "Array Int"
  },
  "verina_precond": "True",
  "verina_code": "let nonZeros := arr.toList.filter (\u00b7 \u2260 0)\n  let zeros := arr.toList.filter (\u00b7 = 0)\n  Array.mk (nonZeros ++ zeros)",
  "verina_postcond": "let firstResZeroIdx := result.toList.idxOf 0\n  List.isPerm result.toList arr.toList \u2227\n  result.toList.take firstResZeroIdx = arr.toList.filter (\u00b7 \u2260 0) \u2227\n  result.toList.drop firstResZeroIdx = arr.toList.filter (\u00b7 = 0)",
  "our_pre": "n >= 0",
  "our_post": "(ForAll(lambda m: Implies(0 <= m and m < n and A[m] != 0, B[nz(A, m)] == A[m]))) and (ForAll(lambda t: Implies(nz(A, n) <= t and t < n, B[t] == 0)))",
  "our_axioms": [
    "nz(A, 0) == 0",
    "ForAll(lambda kk: Implies(kk >= 0 and A[kk] != 0, nz(A, kk + 1) == nz(A, kk) + 1))",
    "ForAll(lambda kk: Implies(kk >= 0 and A[kk] == 0, nz(A, kk + 1) == nz(A, kk)))"
  ],
  "our_outputs": [
    [
      "B",
      "int[]"
    ]
  ]
}
```
