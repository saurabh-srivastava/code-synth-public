# VERINA spec — verina_basic_54

```json
{
  "name": "CanyonSearch",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "b",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Nat"
}
```

```lean
-- precondition
a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

-- reference code
let init : Nat :=
    if a[0]! < b[0]! then (b[0]! - a[0]!).natAbs
    else (a[0]! - b[0]!).natAbs
  canyonSearchAux a b 0 0 init

-- postcondition
(a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))
```
