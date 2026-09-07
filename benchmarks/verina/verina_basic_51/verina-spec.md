# VERINA spec — verina_basic_51

```json
{
  "name": "BinarySearch",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "key",
      "param_type": "Int"
    }
  ],
  "return_type": "Nat"
}
```

```lean
-- precondition
List.Pairwise (· ≤ ·) a.toList

-- reference code
binarySearchLoop a key 0 a.size

-- postcondition
result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))
```
