# VERINA spec — verina_basic_1

```json
{
  "name": "hasOppositeSign",
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
  "return_type": "Bool"
}
```

```lean
-- precondition
True

-- reference code
a * b < 0

-- postcondition
(((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)
```
