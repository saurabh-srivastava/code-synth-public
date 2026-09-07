# VERINA spec — verina_basic_84

```json
{
  "name": "replace",
  "parameters": [
    {
      "param_name": "arr",
      "param_type": "Array Int"
    },
    {
      "param_name": "k",
      "param_type": "Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
True

-- reference code
replace_loop arr k 0 arr

-- postcondition
result.size = arr.size ∧
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
  (∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))
```
