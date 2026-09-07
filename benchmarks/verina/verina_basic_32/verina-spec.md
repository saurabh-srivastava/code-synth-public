# VERINA spec — verina_basic_32

```json
{
  "name": "swapFirstAndLast",
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
let first := a[0]!
  let last := a[a.size - 1]!
  a.set! 0 last |>.set! (a.size - 1) first

-- postcondition
result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)
```
