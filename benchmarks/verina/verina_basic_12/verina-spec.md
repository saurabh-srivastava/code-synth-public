# VERINA spec — verina_basic_12

```json
{
  "name": "cubeSurfaceArea",
  "parameters": [
    {
      "param_name": "size",
      "param_type": "Nat"
    }
  ],
  "return_type": "Nat"
}
```

```lean
-- precondition
True

-- reference code
6 * size * size

-- postcondition
result - 6 * size * size = 0 ∧ 6 * size * size - result = 0
```
