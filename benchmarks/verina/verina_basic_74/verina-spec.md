# VERINA spec — verina_basic_74

```json
{
  "name": "maxArray",
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
maxArray_aux a 1 a[0]!

-- postcondition
(∀ (k : Nat), k < a.size → result >= a[k]!) ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)
```
