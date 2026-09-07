# VERINA spec — verina_basic_47

```json
{
  "name": "arraySum",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Int"
}
```

```lean
-- precondition
a.size > 0

-- reference code
a.toList.sum

-- postcondition
result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size
```
