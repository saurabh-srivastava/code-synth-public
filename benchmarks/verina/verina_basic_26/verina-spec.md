# VERINA spec — verina_basic_26

```json
{
  "name": "isEven",
  "parameters": [
    {
      "param_name": "n",
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
n % 2 == 0

-- postcondition
(result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)
```
