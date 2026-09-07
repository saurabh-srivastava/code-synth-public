# VERINA spec — verina_basic_80

```json
{
  "name": "only_once",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "key",
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
only_once_loop a key 0 0

-- postcondition
((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)
```
