# VERINA spec — verina_basic_99

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
if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    let y := 2 * x
    x + y

-- postcondition
result / 3 = x ∧ result / 3 * 3 = result
```
