# VERINA spec — verina_basic_103

```json
{
  "name": "UpdateElements",
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
a.size ≥ 8

-- reference code
let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2

-- postcondition
result.size = a.size ∧
  result[4]! = (a[4]!) + 3 ∧
  result[7]! = 516 ∧
  (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)
```
