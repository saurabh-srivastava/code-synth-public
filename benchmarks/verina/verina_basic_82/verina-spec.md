# VERINA spec — verina_basic_82

```json
{
  "name": "remove_front",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
a.size > 0

-- reference code
if a.size > 0 then
    let c := copyFrom a 1 (Array.mkEmpty (a.size - 1))
    c
  else
    panic "Precondition violation: array is empty"

-- postcondition
a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)
```
