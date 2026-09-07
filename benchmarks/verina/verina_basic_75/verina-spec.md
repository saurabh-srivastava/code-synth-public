# VERINA spec — verina_basic_75

```json
{
  "name": "minArray",
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
loop a 1 (a[0]!)

-- postcondition
(∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)
```
