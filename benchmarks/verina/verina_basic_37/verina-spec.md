# VERINA spec — verina_basic_37

```json
{
  "name": "findFirstOccurrence",
  "parameters": [
    {
      "param_name": "arr",
      "param_type": "Array Int"
    },
    {
      "param_name": "target",
      "param_type": "Int"
    }
  ],
  "return_type": "Int"
}
```

```lean
-- precondition
List.Pairwise (· ≤ ·) arr.toList

-- reference code
let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0

-- postcondition
(result = -1 ∨ result ≥ 0) ∧
  (result ≥ 0 →
    result.toNat < arr.size ∧
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))
```
