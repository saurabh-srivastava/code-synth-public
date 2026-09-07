# VERINA spec — verina_basic_19

```json
{
  "name": "isSorted",
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
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[i + 1])
      else
        true) |>.all id

-- postcondition
(∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result
```
