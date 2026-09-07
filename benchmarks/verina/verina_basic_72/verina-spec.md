# VERINA spec — verina_basic_72

```json
{
  "name": "append",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    },
    {
      "param_name": "b",
      "param_type": "Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
True

-- reference code
let c_initial := copy a 0 (Array.empty)
  let c_full := c_initial.push b
  c_full

-- postcondition
(List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1
```
