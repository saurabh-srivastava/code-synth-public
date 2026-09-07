# VERINA spec — verina_basic_105

```json
{
  "name": "arrayProduct",
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
  "return_type": "Array Int"
}
```

```lean
-- precondition
a.size = b.size

-- reference code
let len := a.size
  let c := Array.mkArray len 0
  loop a b len 0 c

-- postcondition
(result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)
```
