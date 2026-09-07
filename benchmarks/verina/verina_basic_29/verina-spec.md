# VERINA spec — verina_basic_29

```json
{
  "name": "removeElement",
  "parameters": [
    {
      "param_name": "s",
      "param_type": "Array Int"
    },
    {
      "param_name": "k",
      "param_type": "Nat"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
k < s.size

-- reference code
s.eraseIdx! k

-- postcondition
result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)
```
