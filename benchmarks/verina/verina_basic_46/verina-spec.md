# VERINA spec — verina_basic_46

```json
{
  "name": "lastPosition",
  "parameters": [
    {
      "param_name": "arr",
      "param_type": "Array Int"
    },
    {
      "param_name": "elem",
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
let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (i + 1) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)

-- postcondition
(result = -1 ∨ result ≥ 0) ∧
  (result ≥ 0 →
    result.toNat < arr.size ∧
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))
```
