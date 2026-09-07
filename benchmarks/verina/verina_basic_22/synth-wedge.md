# verina_basic_22 — SYNTH WEDGE

**dissimilarElements** — This task requires writing a Lean 4 method that identifies the dissimilar elements between two arrays of integers. In other words, the method should return an array containing all elements that appear in one input array but not in the other. The output array must contain sorted no duplicate elements.

## Outcome

synth wedged — no solution within 120s wall (25s per-query Z3 budget).  The port's post (sorted + nodup + set-symmetric-difference membership) is faithful, but the set-difference + nodup reasoning over two arrays exceeded the search budget.

## Serialized data

```json
{
  "id": "verina_basic_22",
  "name": "dissimilarElements",
  "category": "synth-wedge",
  "verina_signature": {
    "name": "dissimilarElements",
    "parameters": [
      {
        "param_name": "a",
        "param_type": "Array Int"
      },
      {
        "param_name": "b",
        "param_type": "Array Int"
      }
    ],
    "return_type": "Array Int"
  },
  "verina_precond": "True",
  "verina_code": "let res := a.foldl (fun acc x => if !inArray b x then acc.insert x else acc) Std.HashSet.emptyWithCapacity\n  let res := b.foldl (fun acc x => if !inArray a x then acc.insert x else acc) res\n  (res.toList.mergeSort (\u00b7 \u2264 \u00b7)).toArray",
  "verina_postcond": "result.all (fun x => inArray a x \u2260 inArray b x)\u2227\n  result.toList.Pairwise (\u00b7 \u2264 \u00b7) \u2227\n  List.Nodup result.toList \u2227\n  a.all (fun x => if x \u2208 b then x \u2209 result else x \u2208 result) \u2227\n  b.all (fun x => if x \u2208 a then x \u2209 result else x \u2208 result)",
  "our_pre": "na >= 0 and nb >= 0",
  "our_post": "(ForAll(lambda p: Implies(0 <= p and p < m, ((Exists(lambda j: 0 <= j and j < na and res[p] == a[j])) and not (Exists(lambda j: 0 <= j and j < nb and res[p] == b[j]))) or ((not (Exists(lambda j: 0 <= j and j < na and res[p] == a[j]))) and (Exists(lambda j: 0 <= j and j < nb and res[p] == b[j])))))) and (ForAll(lambda p, q: Implies(0 <= p and p <= q and q < m, res[p] <= res[q]))) and (ForAll(lambda p, q: Implies(0 <= p and p < q and q < m, res[p] != res[q]))) and (ForAll(lambda i: Implies(0 <= i and i < na, Implies(Exists(lambda j: 0 <= j and j < nb and a[i] == b[j]), not (Exists(lambda p: 0 <= p and p < m and res[p] == a[i]))) and Implies(not (Exists(lambda j: 0 <= j and j < nb and a[i] == b[j])), Exists(lambda p: 0 <= p and p < m and res[p] == a[i]))))) and (ForAll(lambda i: Implies(0 <= i and i < nb, Implies(Exists(lambda j: 0 <= j and j < na and b[i] == a[j]), not (Exists(lambda p: 0 <= p and p < m and res[p] == b[i]))) and Implies(not (Exists(lambda j: 0 <= j and j < na and b[i] == a[j])), Exists(lambda p: 0 <= p and p < m and res[p] == b[i])))))",
  "our_axioms": [],
  "our_outputs": [
    [
      "res",
      "int[]"
    ],
    [
      "m",
      "int"
    ]
  ]
}
```
