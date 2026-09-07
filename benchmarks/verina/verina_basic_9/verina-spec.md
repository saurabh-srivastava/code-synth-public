# VERINA spec — verina_basic_9

```json
{
  "name": "hasCommonElement",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "b",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Bool"
}
```

```lean
-- precondition
a.size > 0 ∧ b.size > 0

-- reference code
a.any fun x => b.any fun y => x = y

-- postcondition
(∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result
```
