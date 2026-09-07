# VERINA spec — verina_basic_15

```json
{
  "name": "containsConsecutiveNumbers",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Bool"
}
```

```lean
-- precondition
True

-- reference code
if a.size ≤ 1 then
    false
  else
    let withIndices := a.mapIdx (fun i x => (i, x))
    withIndices.any (fun (i, x) =>
      i < a.size - 1 && x + 1 == a[i+1]!)

-- postcondition
(∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result
```
