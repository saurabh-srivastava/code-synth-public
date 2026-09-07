# VERINA spec — verina_basic_86

```json
{
  "name": "rotate",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "offset",
      "param_type": "Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
offset ≥ 0

-- reference code
let len := a.size
  let default_val : Int := if len > 0 then a[0]! else 0
  let b0 := Array.mkArray len default_val
  rotateAux a offset 0 len b0

-- postcondition
result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)
```
