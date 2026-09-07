# VERINA spec — verina_basic_30

```json
{
  "name": "elementWiseModulo",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "b",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)

-- reference code
a.mapIdx (fun i x => x % b[i]!)

-- postcondition
result.size = a.size ∧
  (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)
```
