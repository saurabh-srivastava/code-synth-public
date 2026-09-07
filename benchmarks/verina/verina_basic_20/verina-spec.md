# VERINA spec — verina_basic_20

```json
{
  "name": "uniqueProduct",
  "parameters": [
    {
      "param_name": "arr",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Int"
}
```

```lean
-- precondition
True

-- reference code
let rec loop (i : Nat) (seen : Std.HashSet Int) (product : Int) : Int :=
    if i < arr.size then
      let x := arr[i]!
      if seen.contains x then
        loop (i + 1) seen product
      else
        loop (i + 1) (seen.insert x) (product * x)
    else
      product
  loop 0 Std.HashSet.empty 1

-- postcondition
result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0
```
