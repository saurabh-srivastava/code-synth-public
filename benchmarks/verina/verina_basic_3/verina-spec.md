# VERINA spec — verina_basic_3

```json
{
  "name": "isDivisibleBy11",
  "parameters": [
    {
      "param_name": "n",
      "param_type": "Int"
    }
  ],
  "return_type": "Bool"
}
```

```lean
-- precondition
True

-- reference code
n % 11 == 0

-- postcondition
(result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))
```
