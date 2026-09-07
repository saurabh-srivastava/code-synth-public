# VERINA spec — verina_basic_106

```json
{
  "name": "arraySum",
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
if a.size ≠ b.size then
    panic! "Array lengths mismatch"
  else
    let n := a.size;
    let c := Array.mkArray n 0;
    let rec loop (i : Nat) (c : Array Int) : Array Int :=
      if i < n then
        let c' := c.set! i (a[i]! + b[i]!);
        loop (i + 1) c'
      else c;
    loop 0 c

-- postcondition
(result.size = a.size) ∧ (∀ i : Nat, i < a.size → a[i]! + b[i]! = result[i]!)
```
