# VERINA spec — verina_basic_55

```json
{
  "name": "Compare",
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
  "return_type": "Bool"
}
```

```lean
-- precondition
True

-- reference code
if a = b then true else false

-- postcondition
(a = b → result = true) ∧ (a ≠ b → result = false)
```
