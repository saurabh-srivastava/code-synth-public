# VERINA spec — verina_basic_53

```json
{
  "name": "CalSum",
  "parameters": [
    {
      "param_name": "N",
      "param_type": "Nat"
    }
  ],
  "return_type": "Nat"
}
```

```lean
-- precondition
True

-- reference code
let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N

-- postcondition
2 * result = N * (N + 1)
```
