# VERINA spec — verina_basic_107

```json
{
  "name": "ComputeAvg",
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
(a + b) / 2

-- postcondition
2 * result = a + b - ((a + b) % 2)
```
