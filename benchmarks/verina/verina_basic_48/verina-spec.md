# VERINA spec — verina_basic_48

```json
{
  "name": "isPerfectSquare",
  "parameters": [
    {
      "param_name": "n",
      "param_type": "Nat"
    }
  ],
  "return_type": "Bool"
}
```

```lean
-- precondition
True

-- reference code
if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n

-- postcondition
result ↔ ∃ i : Nat, i * i = n
```
