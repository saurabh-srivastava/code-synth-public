# VERINA spec — verina_basic_65

```json
{
  "name": "SquareRoot",
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
let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r
    | bound+1, r =>
        if (r + 1) * (r + 1) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0

-- postcondition
result * result ≤ N ∧ N < (result + 1) * (result + 1)
```
