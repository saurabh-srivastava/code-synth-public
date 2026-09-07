# VERINA spec — verina_basic_41

```json
{
  "name": "hasOnlyOneDistinctElement",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Bool"
}
```

```lean
-- precondition
a.size > 0

-- reference code
if a.size = 0 then
    true
  else
    let firstElement := a[0]!
    let rec loop (i : Nat) : Bool :=
      if h : i < a.size then
        if a[i]! = firstElement then loop (i + 1) else false
      else
        true
    loop 1

-- postcondition
let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))
```
