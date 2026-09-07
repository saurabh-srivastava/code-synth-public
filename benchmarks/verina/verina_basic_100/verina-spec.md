# VERINA spec — verina_basic_100

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
if x = 0 then 0 else
    let y := 2 * x
    x + y

-- postcondition
result / 3 = x ∧ result / 3 * 3 = result
```
