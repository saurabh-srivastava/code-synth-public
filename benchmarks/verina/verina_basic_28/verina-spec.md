# VERINA spec — verina_basic_28

```json
{
  "name": "isPrime",
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
n ≥ 2

-- reference code
let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound

-- postcondition
(result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))
```
