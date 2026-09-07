# verina_basic_60 — MIS PORT

**FindEvenNumbers** — This task requires writing a function that processes an array of integers and produces a new array containing only the even numbers from the input. The order of these even numbers should remain the same as in the original array, ensuring that every even number from the input appears in the output and that every element in the output is even.

## Outcome

MIS-PORT.  VERINA's findEvenNumbers RETURNS the array of even elements (order + multiplicity).  The fan-out agent, unable to express the data-dependent-length filter, silently reformulated it as COUNTING the evens — output `c : int`, post `c == count_even(A,n)`. That verifies, but solves a different problem.  Caught by drift_triage.py (output shape scalar != VERINA's Array Int).  A verifying benchmark that answers the wrong question is worse than a failure; excluded from the faithful set.

## Serialized data

```json
{
  "id": "verina_basic_60",
  "name": "FindEvenNumbers",
  "category": "mis-port",
  "verina_signature": {
    "name": "FindEvenNumbers",
    "parameters": [
      {
        "param_name": "arr",
        "param_type": "Array Int"
      }
    ],
    "return_type": "Array Int"
  },
  "verina_precond": "True",
  "verina_code": "let rec loop (i : Nat) (acc : Array Int) : Array Int :=\n    if i < arr.size then\n      if isEven (arr.getD i 0) then\n        loop (i + 1) (acc.push (arr.getD i 0))\n      else\n        loop (i + 1) acc\n    else\n      acc\n  loop 0 (Array.mkEmpty 0)",
  "verina_postcond": "result.all (fun x => isEven x) \u2227\n  result.toList.Sublist arr.toList \u2227\n  result.size = arr.toList.countP isEven",
  "our_pre": "n >= 0",
  "our_post": "c == count_even(A, n)",
  "our_axioms": [
    "count_even(A, 0) == 0",
    "ForAll(lambda k: Implies(k >= 0 and ev(A[k]) == 1, count_even(A, k + 1) == count_even(A, k) + 1))",
    "ForAll(lambda k: Implies(k >= 0 and ev(A[k]) != 1, count_even(A, k + 1) == count_even(A, k)))"
  ],
  "our_outputs": [
    [
      "c",
      "int"
    ]
  ]
}
```
