# verina_basic_52 — PARTIAL FIDELITY

**BubbleSort** — This task requires developing a solution that sorts an array of integers in non-decreasing order. The solution must return an array that is a rearrangement of the input, containing exactly the same elements but ordered from smallest to largest.

## Outcome

sortedness asserted WITHOUT the permutation clause VERINA requires (`List.isPerm result a`).  Our post is `∀p≤q. A[p]≤A[q]` only, so e.g. an all-zeros output would satisfy it.  Verified, but against a spec strictly weaker than VERINA's.

## Serialized data

```json
{
  "id": "verina_basic_52",
  "name": "BubbleSort",
  "category": "partial-fidelity",
  "verina_signature": {
    "name": "BubbleSort",
    "parameters": [
      {
        "param_name": "a",
        "param_type": "Array Int"
      }
    ],
    "return_type": "Array Int"
  },
  "verina_precond": "True",
  "verina_code": "if a.size = 0 then a else bubbleOuter (a.size - 1) a",
  "verina_postcond": "List.Pairwise (\u00b7 \u2264 \u00b7) result.toList \u2227 List.isPerm result.toList a.toList",
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
