# VERINA spec — verina_basic_10

```json
{
  "name": "isGreater",
  "parameters": [
    {
      "param_name": "n",
      "param_type": "Int"
    },
    {
      "param_name": "a",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Bool"
}
```

```lean
-- precondition
a.size > 0

-- reference code
a.all fun x => n > x

-- postcondition
(∀ i, (hi : i < a.size) → n > a[i]) ↔ result
```
