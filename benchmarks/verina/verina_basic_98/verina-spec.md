# VERINA spec — verina_basic_98

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
x * 3

-- postcondition
result / 3 = x ∧ result / 3 * 3 = result
```
