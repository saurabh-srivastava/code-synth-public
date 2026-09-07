# VERINA spec — verina_basic_8

```json
{
  "name": "myMin",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Int"
    },
    {
      "param_name": "b",
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
if a <= b then a else b

-- postcondition
(result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)
```
