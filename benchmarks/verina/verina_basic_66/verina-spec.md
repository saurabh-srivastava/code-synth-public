# VERINA spec — verina_basic_66

```json
{
  "name": "ComputeIsEven",
  "parameters": [
    {
      "param_name": "x",
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
if x % 2 = 0 then true else false

-- postcondition
result = true ↔ ∃ k : Int, x = 2 * k
```
