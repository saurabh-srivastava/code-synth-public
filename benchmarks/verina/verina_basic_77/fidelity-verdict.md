# SpecGen fidelity — verina_basic_77

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_77_modify_array_element
  pre  soundness    XX 0/5
  pre  completeness XX 0/1
  post soundness    XX 0/5
  post completeness XX 0/15
  errors: 26 (first: pre_sound {'A': [[1, 2, 3], [4, 5, 6]], 'index1': 0, 'index2': 1, 'val': 99, 'B': [[1, 2, 3], [4, 5, 6]]}: NameError: name 'm' is not defined)
```
