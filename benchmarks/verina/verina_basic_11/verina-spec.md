# VERINA spec — verina_basic_11

```json
{
  "name": "lastDigit",
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
n % 10

-- postcondition
(0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)
```
