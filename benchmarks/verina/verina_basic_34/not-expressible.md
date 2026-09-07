# verina_basic_34 — NOT EXPRESSIBLE

**findEvenNumbers** — This task requires writing a Lean 4 method that extracts even numbers from an array of integers. The method should return a new array containing only the even numbers found in the input array, while preserving the order in which they appear.

## Outcome

NOT-EXPRESSIBLE (rigorous).  Filter with data-dependent output length + multiplicity + order.  A faithful index-encoded probe wedged 0/63 valid Lean dispatches (52 elaboration errors).  Full analysis in verina/reach-limits/verina_basic_34_findEvenNumbers.md.

## Serialized data

```json
{
  "id": "verina_basic_34",
  "name": "findEvenNumbers",
  "category": "not-expressible",
  "verina_signature": {
    "name": "findEvenNumbers",
    "parameters": [
      {
        "param_name": "arr",
        "param_type": "Array Int"
      }
    ],
    "return_type": "Array Int"
  },
  "verina_precond": "True",
  "verina_code": "arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]",
  "verina_postcond": "result.all (fun x => isEven x \u2227 x \u2208 arr.toList \u2227 result.toList.count x = arr.toList.count x) \u2227\n  arr.all (fun x => isEven x \u2192 x \u2208 result.toList) \u2227\n  arr.all (fun x => arr.all (fun y =>\n    isEven x \u2192 isEven y \u2192\n    arr.toList.idxOf x \u2264 arr.toList.idxOf y \u2192\n    result.toList.idxOf x \u2264 result.toList.idxOf y\n  ))"
}
```
