# VERINA spec — verina_basic_94

```json
{
  "name": "iter_copy",
  "parameters": [
    {
      "param_name": "s",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
True

-- reference code
let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc  -- This case shouldn't happen when i < s.size
    else
      acc
  loop 0 Array.empty

-- postcondition
(s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)
```
