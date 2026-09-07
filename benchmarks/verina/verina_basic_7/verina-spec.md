# VERINA spec — verina_basic_7

```json
{
  "name": "sumOfSquaresOfFirstNOddNumbers",
  "parameters": [
    {
      "param_name": "n",
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
let rec loop (k : Nat) (sum : Nat) : Nat :=
    if k = 0 then
      sum
    else
      loop (k - 1) (sum + (2 * k - 1) * (2 * k - 1))
  loop n 0

-- postcondition
result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0
```
