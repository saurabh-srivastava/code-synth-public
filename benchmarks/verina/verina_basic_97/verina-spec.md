# VERINA spec — verina_basic_97

```json
{
  "name": "TestArrayElements",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "j",
      "param_type": "Nat"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
j < a.size

-- reference code
a.set! j 60

-- postcondition
result.size = a.size ∧
  (result[j]! = 60) ∧ (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)
```
