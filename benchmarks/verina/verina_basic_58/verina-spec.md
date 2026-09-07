# VERINA spec — verina_basic_58

```json
{
  "name": "double_array_elements",
  "parameters": [
    {
      "param_name": "s",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
True

-- reference code
double_array_elements_aux s s 0

-- postcondition
result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!
```
