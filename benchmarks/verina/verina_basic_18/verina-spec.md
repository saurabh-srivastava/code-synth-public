# VERINA spec — verina_basic_18

```json
{
  "name": "sumOfDigits",
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
let rec loop (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc
    else loop (n / 10) (acc + n % 10)
  loop n 0

-- postcondition
result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0
```
