# VERINA spec — verina_basic_68

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
True

-- reference code
let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0

-- postcondition
result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)
```
