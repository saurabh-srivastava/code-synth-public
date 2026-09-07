# VERINA spec — verina_basic_62

```json
{
  "name": "Find",
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
  "return_type": "Int"
}
```

```lean
-- precondition
True

-- reference code
let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0

-- postcondition
(result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)
```
