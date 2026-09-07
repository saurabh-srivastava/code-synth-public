# VERINA spec — verina_basic_57

```json
{
  "name": "CountLessThan",
  "parameters": [
    {
      "param_name": "numbers",
      "param_type": "Array Int"
    },
    {
      "param_name": "threshold",
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
countLessThan numbers threshold

-- postcondition
result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0
```
