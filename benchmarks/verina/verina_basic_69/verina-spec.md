# VERINA spec — verina_basic_69

```json
{
  "name": "LinearSearch",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "e",
      "param_type": "Int"
    }
  ],
  "return_type": "Nat"
}
```

```lean
-- precondition
∃ i, i < a.size ∧ a[i]! = e

-- reference code
linearSearchAux a e 0

-- postcondition
(result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)
```
