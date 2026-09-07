# VERINA spec — verina_basic_56

```json
{
  "name": "copy",
  "parameters": [
    {
      "param_name": "src",
      "param_type": "Array Int"
    },
    {
      "param_name": "sStart",
      "param_type": "Nat"
    },
    {
      "param_name": "dest",
      "param_type": "Array Int"
    },
    {
      "param_name": "dStart",
      "param_type": "Nat"
    },
    {
      "param_name": "len",
      "param_type": "Nat"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len

-- reference code
if len = 0 then dest
  else
    let r := dest
    updateSegment r src sStart dStart len

-- postcondition
result.size = dest.size ∧
  (∀ i, i < dStart → result[i]! = dest[i]!) ∧
  (∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
  (∀ i, i < len → result[dStart + i]! = src[sStart + i]!)
```
