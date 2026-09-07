# VERINA spec — verina_basic_6

```json
{
  "name": "minOfThree",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Int"
    },
    {
      "param_name": "b",
      "param_type": "Int"
    },
    {
      "param_name": "c",
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
if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c

-- postcondition
(result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)
```
