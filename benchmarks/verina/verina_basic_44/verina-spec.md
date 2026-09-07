# VERINA spec — verina_basic_44

```json
{
  "name": "isOddAtIndexOdd",
  "parameters": [
    {
      "param_name": "a",
      "param_type": "Array Int"
    }
  ],
  "return_type": "Bool"
}
```

```lean
-- precondition
True

-- reference code
-- First create pairs of (index, value) for all elements in the array
  let indexedArray := a.mapIdx fun i x => (i, x)

  -- Check if all elements at odd indices are odd numbers
  indexedArray.all fun (i, x) => !(isOdd i) || isOdd x

-- postcondition
result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))
```
