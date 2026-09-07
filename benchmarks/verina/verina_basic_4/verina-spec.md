# VERINA spec — verina_basic_4

```json
{
  "name": "kthElement",
  "parameters": [
    {
      "param_name": "arr",
      "param_type": "Array Int"
    },
    {
      "param_name": "k",
      "param_type": "Nat"
    }
  ],
  "return_type": "Int"
}
```

```lean
-- precondition
k ≥ 1 ∧ k ≤ arr.size

-- reference code
arr[k - 1]!

-- postcondition
arr.any (fun x => x = result ∧ x = arr[k - 1]!)
```
