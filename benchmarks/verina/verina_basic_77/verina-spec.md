# VERINA spec — verina_basic_77

```json
{
  "name": "modify_array_element",
  "parameters": [
    {
      "param_name": "arr",
      "param_type": "Array (Array Nat)"
    },
    {
      "param_name": "index1",
      "param_type": "Nat"
    },
    {
      "param_name": "index2",
      "param_type": "Nat"
    },
    {
      "param_name": "val",
      "param_type": "Nat"
    }
  ],
  "return_type": "Array (Array Nat)"
}
```

```lean
-- precondition
index1 < arr.size ∧
  index2 < (arr[index1]!).size

-- reference code
let inner := arr[index1]!
  let inner' := updateInner inner index2 val
  arr.set! index1 inner'

-- postcondition
result.size = arr.size ∧
  (result[index1]!).size = (arr[index1]!).size ∧
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
  (∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
  ((result[index1]!)[index2]! = val)
```
