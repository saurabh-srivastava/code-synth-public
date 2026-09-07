# VERINA spec — verina_basic_76

```json
{
  "name": "myMin",
  "parameters": [
    {
      "param_name": "x",
      "param_type": "Int"
    },
    {
      "param_name": "y",
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
if x < y then x else y

-- postcondition
(x ≤ y → result = x) ∧ (x > y → result = y)
```
