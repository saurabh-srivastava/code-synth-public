# VERINA spec — verina_basic_40

```json
{
  "name": "secondSmallest",
  "parameters": [
    {
      "param_name": "s",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Int"
}
```

```lean
-- precondition
s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!  -- at least two distinct values

-- reference code
secondSmallestAux s 1 0 none

-- postcondition
(∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)
```
