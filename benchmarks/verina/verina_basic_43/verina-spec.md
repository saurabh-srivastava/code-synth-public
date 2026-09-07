# VERINA spec — verina_basic_43

```json
{
  "name": "sumOfFourthPowerOfOddNumbers",
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
match n with
  | 0 => 0
  | n + 1 =>
    let prev := sumOfFourthPowerOfOddNumbers n h_precond
    let nextOdd := 2 * n + 1
    prev + nextOdd^4

-- postcondition
15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)
```
