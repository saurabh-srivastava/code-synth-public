# VERINA spec — verina_basic_101

```json
{
  "name": "Triple",
  "parameters": [
    {
      "param_name": "x",
      "param_type": "Int"
    }
  ],
  "return_type": "Int"
}
```

```lean
-- precondition
True

-- reference code
let y := x * 2
  y + x

-- postcondition
result / 3 = x ∧ result / 3 * 3 = result
```
