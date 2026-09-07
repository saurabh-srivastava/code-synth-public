# VERINA spec — verina_basic_5

```json
{
  "name": "multiply",
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
a * b

-- postcondition
result - a * b = 0 ∧ a * b - result = 0
```
