# VERINA spec — verina_basic_23

```json
{
  "name": "differenceMinMax",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Int"
}
```

```lean
-- precondition
a.size > 0

-- reference code
let rec loop (i : Nat) (minVal maxVal : Int) : Int :=
    if i < a.size then
      let x := a[i]!
      let newMin := if x < minVal then x else minVal
      let newMax := if x > maxVal then x else maxVal
      loop (i + 1) newMin newMax
    else
      maxVal - minVal
  loop 1 (a[0]!) (a[0]!)

-- postcondition
result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))
```
