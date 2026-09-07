# VERINA spec — verina_basic_50

```json
{
  "name": "Abs",
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
if x < 0 then -x else x

-- postcondition
(x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)
```
