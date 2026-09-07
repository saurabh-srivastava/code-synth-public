# VERINA spec — verina_basic_13

```json
{
  "name": "cubeElements",
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
True

-- reference code
a.map (fun x => x * x * x)

-- postcondition
(result.size = a.size) ∧
  (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)
```
