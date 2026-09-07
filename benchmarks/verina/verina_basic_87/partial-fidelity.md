# verina_basic_87 — PARTIAL FIDELITY

**SelectionSort** — This problem requires sorting an array of integers into non-decreasing order, ensuring that the output contains exactly the same elements as the input (i.e., it is a permutation of the original array).

## Outcome

same as BubbleSort: our post asserts sortedness only, not that the result is a permutation of the input.

## Serialized data

```json
{
  "id": "verina_basic_87",
  "name": "SelectionSort",
  "category": "partial-fidelity",
  "verina_signature": {
    "name": "SelectionSort",
    "parameters": [
      {
        "param_name": "a",
        "param_type": "Array Int"
      }
    ],
    "return_type": "Array Int"
  },
  "verina_precond": "True",
  "verina_code": "let indices := List.range a.size\n  indices.foldl (fun arr i =>\n    let minIdx := findMinIndexInRange arr i a.size\n    swap arr i minIdx\n  ) a",
  "verina_postcond": "List.Pairwise (\u00b7 \u2264 \u00b7) result.toList \u2227 List.isPerm a.toList result.toList",
  "our_pre": "n >= 0",
  "our_post": "ForAll(lambda p, q: Implies(0 <= p and p <= q and q < n, A[p] <= A[q]))",
  "our_axioms": [],
  "our_outputs": [
    [
      "A",
      "int[]"
    ]
  ]
}
```
