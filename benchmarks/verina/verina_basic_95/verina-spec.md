# VERINA spec — verina_basic_95

```json
{
  "name": "swap",
  "parameters": [
    {
      "param_name": "arr",
      "param_type": "Array Int"
    },
    {
      "param_name": "i",
      "param_type": "Int"
    },
    {
      "param_name": "j",
      "param_type": "Int"
    }
  ],
  "return_type": "Array Int"
}
```

```lean
-- precondition
i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size

-- reference code
let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2

-- postcondition
result.size = arr.size ∧
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)
```
